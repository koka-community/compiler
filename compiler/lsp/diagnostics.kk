// `textDocument/publishDiagnostics` and `textDocument/diagnostic`.
//
// Split out of `server.kk` to mirror upstream's one-file-per-handler
// `LanguageServer/Handler/` layout.
module compiler/lsp/diagnostics

import std/os/path
import std/core/undiv
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/file
import compiler/compile/options
import compiler/compile/build-context
import compiler/syntax/range-map
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/type/assumption
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
import std/async
import compiler/common/parse
import compiler/common/color-scheme
import compiler/compile/vfs
import compiler/syntax/syntax
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/compile/build
import compiler/lsp/util

// What one check of a document produced. (A plain tuple would do, but Koka has
// no 6-tuple type -- and the names read better at the use site anyway.)
pub type check-result
  CheckResult(
    sess: session,
    rmap: range-map,
    gam: gamma,
    prog: maybe<user-program>,
    ntypes: newtypes,
    syns: synonyms,
    diags: list<json>,
    note: string)

// Type-check the document from the OVERLAY (never from disk) and turn whatever
// the compiler reports into a `publishDiagnostics` notification.
pub fun diagnostics-for(st: server-state, d: state/doc, revalidate: bool = False,
                    // row spelled out to match `check-file-ex`'s own parameter: the
                    // call site sits inside `var` scopes, so an inferred row would
                    // pick up their `local<h>` and fail to unify
                    cancelled: () -> <io,async,comp-error,parse-error,vfs-lookup> bool = fn() False): _ check-result
  val p = d.uri.uri-to-path
  var msgs : errors := []
  val fl = st.flags
  // the abortive handlers below must produce `()`, so the compile runs in its
  // own function and the notification is built from `msgs` afterwards
  var sess2 : session := st.sess
  // a `ref`, not a `var`: the capture callback below is handed to the build,
  // whose row has no `local<h>` -- `read`/`write<global>` are already part of io
  val rmap : ref<global,range-map> = ref([])
  val gam : ref<global,gamma> = ref(gamma/new([]))
  val prog : ref<global,maybe<user-program>> = ref(Nothing)
  val ntypes : ref<global,newtypes> = ref(newtypes/empty)
  val syns : ref<global,synonyms> = ref(synonyms/empty)
  // The analysis compile is the one the user waits on most often (it runs on
  // every idle after an edit) and it had no progress token at all, so nothing
  // it did was visible. Same treatment as `koka/compile`.
  val token = "koka/check"
  val last-pct : ref<global,int> = ref(0)
  fun report(done: int, total: int, _nm: name): _ ()
    last-pct.set(if total <= 0 then 0 else (100 * done) / total)
  fun compile-it(): _ ()
    with with-lsp-progress(st.flags.verbose, token, last-pct)
    with no-vfs
    // EVERY open document, not just the one being checked: an edited-but-
    // unsaved import has to be visible when its dependents are analysed, which
    // is the whole reason the build reads through an overlay.
    with with-vfs(st.overlay)
    with handler
      final ctl parse-error(e: string, r: range)
        msgs := msgs ++ [ErrorMsg(r, e.text, SevError, ErrGeneral)]
        ()
    with handler
      final ctl add-errors(errs: errors)
        msgs := msgs ++ errs
        ()
      fun add-warnings(w: errors) msgs := msgs ++ w
      fun add-infos(w: errors) msgs := msgs ++ w
    // analysis only: a language server must never link or run anything
    // the edited buffer's own module must be reloaded from the overlay; a
    // timestamp sweep would not catch it, since nothing on disk moved
    val sess1 = st.sess.session-invalidate(p)
    val sess0 = if revalidate then sess1.session-revalidate(fl) else sess1
    fun capture(ModuleCheck(_nm, rm, g, pr, nts, sy, _kg): module-check)
      rmap.set(rm)
      gam.set(g)
      prog.set(Just(pr))
      ntypes.set(nts)
      syns.set(sy)
    match try({ check-file-session(fl(evaluate = False, library = True, typeCheckOnly = True), p.string, sess0, cancelled = cancelled, on-range-map = capture, on-progress = report) })
      Error(exn) ->
        // A parse error reaches us as an EXCEPTION carrying an already-formatted
        // message (`syntax/parse.kk`'s `show-parse-error` throws rather than
        // re-raising through the `parse-error` effect), so the range has to be
        // recovered from the text -- otherwise every syntax error lands at the
        // top of the file instead of where it is.
        msgs := msgs ++ [ErrorMsg(exn.message.error-position(p), exn.message.strip-location.text, SevError, ErrGeneral)]
      Ok(s2) -> sess2 := s2
  write-bytes(progress-create(token).frame)
  write-bytes(progress-begin(token, "Koka: checking " ++ p.basename).frame)
  compile-it()
  write-bytes(progress-end(token, "").frame)
  // Diagnostics also go to the log channel. They are
  // already delivered as `publishDiagnostics` for the squiggles; this is the
  // human-readable copy in the server's terminal -- and it is what makes the
  // extension focus that terminal, since its `appendLine` calls `show()` only
  // when the text matches /error/i.
  msgs.foreach fn(e)
    write-bytes(log-diagnostic(e.err/show, e.severity.severity/to-lsp <= 1).frame)
  val items = msgs.map(to-diagnostic)
  CheckResult(sess2, !rmap, !gam, !prog, !ntypes, !syns, items, publish-diagnostics(d.uri, items))

pub fun to-diagnostic(e: error-msg): _ json
  JSObj([
    ("range", e.range.range/to-lsp),
    ("severity", JSInt(e.severity.severity/to-lsp)),
    ("source", JSString("koka")),
    ("message", JSString(e.message.show))
  ])

pub fun publish-diagnostics(uri: string, ds: list<json>): string
  notification("textDocument/publishDiagnostics",
               JSObj([("uri", JSString(uri)), ("diagnostics", JSList(ds))]))
