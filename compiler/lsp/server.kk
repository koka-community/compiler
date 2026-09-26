// Language server: document synchronisation and diagnostics.
//
// The editor's buffer, not the file on disk, is the source of truth while a
// document is open -- that is exactly what `compiler/compile/vfs.kk` provides,
// so `didOpen`/`didChange` maintain an overlay and every compile runs against
// it. A file with unsaved edits therefore type-checks as the user sees it.
//
// Only whole-document sync is implemented (`textDocumentSync: 1`): incremental
// sync would need range-based edits applied to the buffer, and there is no
// reason to take that on before the basics are proven.
module compiler/lsp/server

import std/os/path
import std/data/rb-map
import std/async
import std/core/undiv
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/parse
import compiler/common/color-scheme
import compiler/common/file
import compiler/platform/config
import compiler/compile/options
import compiler/compile/build
import compiler/compile/build-context
import compiler/compile/vfs
import compiler/syntax/range-map
import compiler/type/assumption
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/type/pretty
import compiler/kind/pretty
import compiler/kind/kind
import compiler/lib/pprint
import compiler/lib/json
import compiler/lib/log
import compiler/lsp/jsonrpc
import compiler/lsp/stdio
import compiler/lsp/conversions
import compiler/lsp/state
import compiler/lsp/util
import compiler/lsp/diagnostics
import compiler/lsp/hover
import compiler/lsp/inlay-hints
import compiler/lsp/definition
import compiler/lsp/symbols
import compiler/lsp/commands
import compiler/lsp/completion
import compiler/lsp/signature-help
import compiler/lsp/code-action

pub fun run(fl0: flags): <io,async,colors,comp-flags> ()
  with collapse-div
  // FIRST, before anything can print: fd 1 belongs to the protocol from here on,
  // and every `println` in the compiler is rerouted to stderr. The build has
  // unconditional prints on its failure paths ("link failed for ...") which
  // would otherwise land in the middle of a JSON-RPC frame and drop the
  // connection -- precisely when a compile has gone wrong.
  claim-stdout()
  // Phase logging becomes `window/logMessage`, which the editor shows in the
  // server's output channel -- upstream's language-server `Terminal` does the
  // same. Set before the build can spawn a worker; see `lib/log.kk`'s contract.
  // Phase logging becomes `window/logMessage`, which the editor shows in the
  // server's output channel -- upstream's language-server Terminal does the
  // same, gated on the same verbosity.
  with with-lsp-phase(fl0.verbose)
  // `--showtypesigs` / `--showcore` output is meaningless to an editor, and fd 1
  // here is the PROTOCOL -- writing it there drops the connection mid-frame.
  // `claim-stdout` already reroutes bare `println`s to stderr; giving this class
  // of output its own channel makes that a typed guarantee rather than a
  // consequence of an fd trick. Installed AFTER the phase handler so it can
  // forward into it.
  with fun emit-line(s: string) log-phase(1, "", s)
  // A language server compiles UNSAVED buffers, so its `.kki`/`.c` artifacts
  // describe code that does not exist on disk. Writing those into the ordinary
  // build directory would let a later `koka -c` consume an interface built from
  // edits the user never saved, so the session gets its own output directory.
  val fl = fl0(buildTag = if fl0.buildTag.is-empty then "lsp" else fl0.buildTag ++ "-lsp")
  //
  // TWO STRANDS.
  //
  // The reader pushes every framed payload onto `inbox` and never waits for the
  // worker; the worker drains `inbox`, answers what it can immediately, and
  // defers compiles until the inbox is empty. Both are green threads, so they
  // interleave at await points -- and the compile has plenty (the RPC
  // orchestrator awaits its worker threads), which is what lets a request be
  // answered, and a newer edit be noticed, WHILE a compile is running.
  //
  // `edits` is how a newer edit takes effect: the worker snapshots it before a
  // compile and the orchestrator polls for a change between module dispatches,
  // so a superseded compile stops at the next module boundary. Modules already
  // in flight finish, so no half-written interface is left behind.
  val inbox = channel()
  val edits : ref<global,int> = ref(0)
  interleaved
    // The READER bumps the counter, not the worker: during a compile the worker
    // is not processing messages, so a worker-side bump could never fire while
    // it mattered.
    //
    // ONLY A CONTENT CHANGE BUMPS IT. It used to bump on ANY message, on the
    // reasoning that a request arriving mid-compile is at least delaying an
    // answer. But a superseded compile is DISCARDED and its document re-marked
    // dirty (see `on-idle`), and this server advertises `diagnosticProvider`
    // and `inlayHintProvider`, so an editor polls it continuously. Every
    // compile was therefore cancelled by the next poll and restarted, forever:
    // measured on `compiler/syntax/lexeme.kk` with a 1s poll, 118 compiles in
    // 150s, 118 of them superseded, not one result ever stored. That is the
    // "it just keeps reloading the file" loop.
    //
    // A request cannot invalidate a compile -- it is answered from the last
    // stored result -- so it must not cancel one. Upstream only rebuilds on
    // `didOpen`/`didChange` too (`LanguageServer/Handler/TextDocument.hs`).
    //
    // Matching on the QUOTED method name is deliberate: a document's text is
    // JSON-escaped inside the payload (`\"method\"`), so source that mentions
    // these names -- this file, for one -- cannot match. Under-matching is the
    // safe direction anyway: the worst case is an in-flight compile that is not
    // cancelled, and the edit has already marked the document dirty, so the
    // next idle pass redoes it. Over-matching is what loops.
    { read-loop({ read-chunk() }, fn(mb) on-payload(mb, edits, inbox)) }
    { work-loop(fl, inbox, edits) }
  ()

fun on-payload(mb: maybe<string>, edits: ref<global,int>, inbox: channel<maybe<string>>): _ ()
  match mb
    Just(payload) ->
      if payload.invalidates-compile then edits.set(!edits + 1)
      inbox.emit(mb)
    Nothing -> inbox.emit(mb)

// Does this message change document CONTENT, and so invalidate a compile that
// is already running? Notifications only -- a request never does.
fun invalidates-compile(payload: string): bool
  payload.find("\"textDocument/didChange\"").is-just ||
  payload.find("\"textDocument/didOpen\"").is-just

fun work-loop(fl: flags, inbox: channel<maybe<string>>, edits: ref<global,int>): _ ()
  fun dispatch(st: server-state, payload: string): _ maybe<server-state>
    val (mbst, outs) = match try({ payload.parse-message })
      Ok(m) -> on-message(st, m)
      Error(err) -> (Just(st), [error-response(JSNull, parse-error-code, err.message)])
    outs.foreach(fn(out) write-bytes(out.frame))
    match mbst
      Just(st2) -> Just(st2)
      Nothing -> Nothing
  fun go(st: server-state)
    match inbox.try-receive
      Just(Just(payload)) ->
        match dispatch(st, payload)
          Just(st2) -> go(st2)
          Nothing -> ()                        // `exit`
      Just(Nothing) -> ()                      // end of input
      Nothing ->
        // inbox drained: compile what is dirty, then block for the next message
        val (st2, outs) = st.on-idle(edits)
        outs.foreach(fn(out) write-bytes(out.frame))
        match inbox.receive
          Just(payload) ->
            match dispatch(st2, payload)
              Just(st3) -> go(st3)
              Nothing -> ()
          Nothing -> ()
  go(new-state(fl))

fun on-message(st: server-state, msg: message): _ (maybe<server-state>, list<string>)
  match msg
    Request(id, "initialize", ps) ->
      // remember the roots exactly as the client spelled them; every URI we
      // report later is rebuilt in those terms, never from the server's cwd
      val folders = match ps.field("workspaceFolders")
        Just(JSList(fs)) -> fs.map(fn(f) f.field("uri").as-string.default("")).filter(fn(u) !u.is-empty)
        _ -> match ps.field("rootUri").as-string
          Just(u) | !u.is-empty -> [u]
          _ -> []
      (Just(st.with-roots(folders)), [response(id, initialize-result())])
    Request(id, "shutdown", _) ->
      (Just(st(shutting-down = True)), [response(id, JSNull)])
    Notification("exit", _) ->
      (Nothing, [])                            // ends the serve loop
    Notification("initialized", _) -> (Just(st), [])
    Notification("textDocument/didOpen", ps) ->
      match ps.field("textDocument")
        Just(td) ->
          val d = opened-doc(td.field("uri").as-string.default(""),
                             td.field("text").as-string.default(""),
                             td.field("version").as-int.default(0))
          (Just(st.put-doc(d).mark-dirty(d.uri)), [])
        Nothing -> (Just(st), [])
    Notification("textDocument/didChange", ps) ->
      val duri = ps.field("textDocument").field-of("uri").as-string.default("")
      // whole-document sync: the last content change carries the full text
      val text = match ps.field("contentChanges")
        Just(JSList(cs)) -> cs.reverse.head.field-of("text").as-string.default("")
        _ -> ""
      val ver = ps.field("textDocument").field-of("version").as-int.default(0)
      val d = edited-doc(st.find-doc(duri), duri, text, ver)
      (Just(st.put-doc(d).mark-dirty(duri)), [])
    Notification("textDocument/didSave", ps) ->
      // buffer and file agree again; re-stamp the overlay from the file so the
      // saved content is not treated as perpetually newer than its interface
      val duri = ps.field("textDocument").field-of("uri").as-string.default("")
      match st.find-doc(duri)
        Just(d) -> (Just(st.put-doc(d.saved-doc)), [])
        Nothing -> (Just(st), [])
    Notification("workspace/didChangeConfiguration", ps) ->
      // The client pushes settings (target, include dirs, inlay-hint toggles).
      // Only the inlay-hint toggles are consumed; the rest are acknowledged so
      // the client does not treat the server as unresponsive to them.
      val hints = ps.field("settings").field-of("koka")
                    .field-of("languageServer").field-of("inlayHints")
      fun toggle(k: string, cur: bool): bool
        hints.field-of(k).as-bool.default(cur)
      (Just(st(hint-implicits = toggle("showImplicitArguments", st.hint-implicits),
               hint-types     = toggle("showInferredTypes", st.hint-types),
               hint-qualifiers = toggle("showFullQualifiers", st.hint-qualifiers))), [])
    Notification("textDocument/didClose", ps) ->
      val duri = ps.field("textDocument").field-of("uri").as-string.default("")
      // clear the editor's squiggles for a document we no longer track
      (Just(st.remove-doc(duri)), [publish-diagnostics(duri, [])])
    Request(id, "workspace/executeCommand", ps) ->
      match st.execute-command(ps)
        Just((st2, res)) -> (Just(st2), [response(id, res)])
        Nothing ->
          val cmd = ps.field("command").as-string.default("")
          (Just(st), [error-response(id, method-not-found-code, "unsupported command: " ++ cmd)])
    Request(id, "textDocument/diagnostic", ps) ->
      // PULL diagnostics (LSP 3.17). The client uses this because we advertise
      // `diagnosticProvider`; answering -32601 while still pushing on every edit
      // is what produced "unsupported method: textDocument/diagnostic" in the
      // client log even though diagnostics appeared. Served from the last
      // compile's result rather than recompiling, so a pull is free.
      val duri = ps.field("textDocument").field-of("uri").as-string.default("")
      val items = match st.find-doc(duri)
        Just(d) -> d.diags
        Nothing -> []
      (Just(st), [response(id, JSObj([("kind", JSString("full")), ("items", JSList(items))]))])
    Request(id, "textDocument/inlayHint", ps) ->
      (Just(st), [response(id, st.inlay-hints(ps))])
    Request(id, "textDocument/definition", ps) ->
      (Just(st), [response(id, st.definition(ps))])
    Request(id, "textDocument/hover", ps) ->
      (Just(st), [response(id, st.hover(ps))])
    Request(id, "textDocument/codeAction", ps) ->
      (Just(st), [response(id, st.code-actions(ps))])
    Request(id, "textDocument/signatureHelp", ps) ->
      (Just(st), [response(id, st.signature-help(ps))])
    Request(id, "textDocument/completion", ps) ->
      (Just(st), [response(id, st.completion(ps))])
    Request(id, "textDocument/documentSymbol", ps) ->
      (Just(st), [response(id, st.with-program(ps, program/symbols))])
    Request(id, "textDocument/foldingRange", ps) ->
      (Just(st), [response(id, st.with-program(ps, program/foldings))])
    Request(id, m, _) ->
      (Just(st), [error-response(id, method-not-found-code, "unsupported method: " ++ m)])
    Notification(_m, _) -> (Just(st), [])
    // an answer to something WE asked for; nothing to do with it
    Response(_) -> (Just(st), [])

// Check every document marked dirty, once, now that the input buffer has
// drained. A burst of N keystrokes therefore costs ONE compile, not N.
fun on-idle(st: server-state, edits: ref<global,int>): _ (server-state, list<string>)
  if st.dirty.is-nil then (st, [])
  else
    val (st2, notes) = st.dirty.foldl((st.clear-dirty, [])) fn((sti, acc), u)
      match sti.find-doc(u)
        Nothing -> (sti, acc)
        Just(d) ->
          // Snapshot the edit counter FIRST: `superseded` must be false at the
          // start of this compile and become true only if a NEW edit arrives
          // while it runs. (Comparing against the dirty list instead made it
          // true immediately, which cancelled every compile before it began.)
          val seen = !edits
          fun superseded() !edits != seen
          // opening a document is the moment an external change on disk is
          // plausible, so revalidate the session then; an edit only changed the
          // buffer, which the overlay already reflects
          val CheckResult(sess2, rm, g, pr, nts, sy, items, note) = sti.diagnostics-for(d, d.rmap.is-nil, superseded)
          // a superseded compile has partial diagnostics: do not publish them,
          // and leave the document dirty so the next idle pass redoes it
          // A check that failed outright (a syntax error while typing is the
          // common case) produces NO range map. Keeping the previous one is
          // what lets hover, completion and inlay hints keep working through a
          // half-typed line; overwriting with the empty result made every
          // feature go blank on the very edit the user needs help with.
          val d2 = if rm.is-nil && !d.rmap.is-nil then d(diags = items)
                   else d(rmap = rm, gam = g, prog = pr, ntypes = nts, syns = sy, diags = items)
          if timing-on() then println("ONIDLE store: " ++ sess2.mods.list.length.show ++ " modules, superseded=" ++ superseded().show)
          if superseded() then (sti.mark-dirty(u), acc)
          else (sti(sess = sess2).put-doc(d2), acc ++ [note])
    (st2, notes)

// Answer `textDocument/completion` from the last check's range map and gamma.
fun completion(st: server-state, ps: json): _ json
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSObj([("isIncomplete", JSBool(False)), ("items", JSList([]))])
    Just(d) ->
      val p = ps.field("position").pos/from-lsp(Source(duri.uri-to-path.string, ""))
      val lexemes = lexer(duri.uri-to-path.string, 1, d.text)
      val modname = d.uri.uri-to-path.stemname.new-module-name
      d.completions-for(p, lexemes, modname)

fun initialize-result(): json
  JSObj([("capabilities", JSObj([
    ("textDocumentSync", JSInt(1)),          // 1 = full document sync
    ("hoverProvider", JSBool(True)),
    ("definitionProvider", JSBool(True)),
    ("inlayHintProvider", JSObj([("resolveProvider", JSBool(False))])),
    ("documentSymbolProvider", JSBool(True)),
    ("codeActionProvider", JSBool(True)),
    // upstream registers the same trigger/retrigger characters
    ("signatureHelpProvider", JSObj([
       ("triggerCharacters", JSList([JSString("("), JSString(","), JSString(" ")])),
       ("retriggerCharacters", JSList([JSString(")")]))])),
    // `.` re-triggers so a dot-call offers members immediately
    ("completionProvider", JSObj([("triggerCharacters",
       JSList([".", ":", "/", " ", "]", "}"].map(JSString))),
                                  ("resolveProvider", JSBool(False))])),
    ("foldingRangeProvider", JSBool(True)),
    // the extension's run/debug code lenses drive these; a client only sends a
    // command the server advertises here
    ("executeCommandProvider", JSObj([("commands", JSList(command-names.map(JSString)))])),
    ("diagnosticProvider", JSObj([("interFileDependencies", JSBool(True)),
                                  ("workspaceDiagnostics", JSBool(False))]))
  ]))])
