// Language server state.
//
// Everything the server remembers between requests, plus the operations that
// maintain it. Kept apart from `server.kk` so protocol handling stays a thin
// layer over well-defined state transitions -- every feature added later
// (definition, symbols, inlay hints) reads this same table rather than growing
// its own bookkeeping.
module compiler/lsp/state

import std/os/path
import compiler/common/name
import compiler/common/file
import compiler/compile/options
import compiler/compile/build-context
import compiler/compile/vfs
import compiler/type/assumption
import compiler/syntax/range-map
import compiler/syntax/syntax
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/lsp/conversions
import compiler/lib/json

// One open editor buffer. While a document is open THIS is the source of
// truth, not the file on disk.
pub struct doc
  uri: string
  text: string
  version: int
  // epoch seconds, comparable with `file-mtime`. On open it is the FILE's
  // timestamp (the buffer matches disk, so nothing needs recompiling); on edit
  // it is the edit time (the buffer is now newer than anything built from it).
  // The build's staleness checks see this through the overlay -- a version
  // counter here would be meaningless against on-disk interface times.
  mtime: int
  // the type checker's range map from the last check of this buffer; answers
  // hover and definition
  rmap: range-map = []
  // the PARSED program from that same check. Document symbols and folding are
  // pure syntax-tree walks, and nothing downstream of type checking keeps the
  // tree, so it is captured alongside the range map.
  prog: maybe<user-program> = Nothing
  // the module's data types, by name: code actions generate `show`/`==`/... for
  // whichever one the cursor is inside
  ntypes: newtypes = newtypes/empty
  // type synonyms, offered in a type position
  syns: synonyms = synonyms/empty
  // the module's gamma from that same check: resolves a name under the cursor
  // to the range where it was defined
  gam: gamma = gamma/new([])
  // the diagnostics last published for this buffer. Kept so `textDocument/
  // diagnostic` (the PULL model, which the client uses because we advertise
  // `diagnosticProvider`) can answer without recompiling.
  diags: list<json> = []

pub struct server-state
  flags: flags
  docs: list<doc>
  shutting-down: bool = False
  // resolved modules + dependency scan carried across requests; see `session`
  // in compile/build-context.kk for why this matters so much
  sess: session = Session()
  // Workspace roots exactly as the CLIENT named them: (root path, root uri).
  // A URI we hand back must be in the client's own vocabulary -- with multiple
  // roots, symlinked checkouts, or a differently-cased drive, a URI rebuilt
  // from the server's cwd names a file the client will not recognise.
  roots: list<(path, string)> = []
  // The overload the client last accepted from a completion, set by the
  // `koka/signature-help/set-context` command. Signature help makes it the
  // ACTIVE signature -- otherwise accepting one overload and then typing its
  // arguments shows a different overload's parameters.
  sig-context: maybe<string> = Nothing
  // `koka.languageServer.inlayHints.*`, pushed by the client through
  // `workspace/didChangeConfiguration`. Upstream's `InlayHintOptions`; each
  // kind of hint is a separate toggle and all three default ON.
  hint-implicits: bool = True
  hint-types: bool = True
  hint-qualifiers: bool = True
  // documents whose diagnostics are out of date. Edits mark a document dirty
  // rather than compiling on the spot: a burst of keystrokes arrives as many
  // messages, and checking each one produces results that the next keystroke
  // immediately supersedes. The idle pass (see `serve`'s `on-idle`) compiles
  // each dirty document ONCE, after the input buffer has drained.
  dirty: list<string> = []

pub fun new-state(fl: flags): server-state
  Server-state(fl, [], False, Session(), [], Nothing, True, True, True, [])

//----------------------------------------------------------------------
// the document table
//----------------------------------------------------------------------

pub fun find-doc(st: server-state, u: string): maybe<doc>
  st.docs.find(fn(d) d.uri == u)

// Insert or replace, keeping at most one entry per uri.
pub fun put-doc(st: server-state, d: doc): server-state
  st(docs = Cons(d, st.docs.filter(fn(o) o.uri != d.uri)))

pub fun remove-doc(st: server-state, u: string): server-state
  st(docs = st.docs.filter(fn(o) o.uri != u), dirty = st.dirty.filter(fn(x) x != u))

pub fun mark-dirty(st: server-state, u: string): server-state
  if st.dirty.any(fn(x) x == u) then st else st(dirty = st.dirty ++ [u])

pub fun clear-dirty(st: server-state): server-state
  st(dirty = [])

// A buffer that has just been opened: it matches the file, so it carries the
// file's timestamp and nothing is needlessly recompiled.
pub fun opened-doc(u: string, text: string, version: int): _ doc
  val ft = u.uri-to-path.file/file-mtime
  Doc(u, text, version, if ft > 0 then ft else epoch-nanos(), [], Nothing, newtypes/empty, synonyms/empty, gamma/new([]), [])

// A buffer that has just been edited: it is newer than any artifact built from
// the previous content.
//
// The ANALYSIS of the previous content is carried forward -- only the text,
// version and timestamp change. An edit is the moment a buffer most often stops
// parsing (`[1, 2].` the instant the `.` lands), and the next check then
// produces nothing; without the old range map and gamma to fall back on, every
// type-driven feature goes dark exactly when it is being asked for. Building a
// blank doc here also silently defeated the same fallback in `on-idle`.
pub fun edited-doc(prev: maybe<doc>, u: string, text: string, version: int): _ doc
  match prev
    Just(d) -> d(text = text, version = version, mtime = epoch-nanos())
    Nothing -> Doc(u, text, version, epoch-nanos(), [], Nothing, newtypes/empty, synonyms/empty, gamma/new([]), [])

// A buffer that has just been SAVED. Buffer and file agree again, so the
// overlay takes the file's (new) timestamp -- otherwise the edit-time stamp
// keeps looking newer than any interface legitimately rebuilt from the saved
// file, and the module is recompiled on every later check for nothing.
pub fun saved-doc(d: doc): _ doc
  val ft = d.uri.uri-to-path.file/file-mtime
  if ft > 0 then d(mtime = ft) else d

//----------------------------------------------------------------------
// uris
//----------------------------------------------------------------------

// Record the roots the client declared at `initialize` (`workspaceFolders`,
// else `rootUri`).
pub fun with-roots(st: server-state, uris: list<string>): _ server-state
  st(roots = uris.map(fn(u) (u.uri-to-path, u)))

// The URI to report for `p`, in the client's own terms:
//   1. a document the client opened -- reuse the very URI it sent
//   2. a file under a declared root -- rebuild from that ROOT's uri
//   3. otherwise -- a plain absolute `file:` uri
// Only (3) invents anything, and only for a file the client never named.
pub fun client-uri(st: server-state, p: path): io string
  val ps = p.canon
  match st.docs.find(fn(d) d.uri.uri-to-path.canon == ps)
    Just(d) -> d.uri
    Nothing ->
      match st.roots.find(fn((rp, _)) ps.starts-with(rp.canon ++ "/").bool)
        Just((rp, ru)) ->
          val rel = ps.list.drop(rp.canon.count + 1).string
          (if ru.ends-with("/").bool then ru else ru ++ "/") ++ rel
        Nothing -> p.path-to-uri

// `realpath` only resolves paths that exist; a virtual or not-yet-written path
// falls back to its own spelling.
fun canon(p: path): io string
  match try({ p.realpath })
    Ok(r) -> r.string
    Error -> p.string

//----------------------------------------------------------------------
// the source overlay
//----------------------------------------------------------------------

// EVERY open document, not just the one being checked: an edited-but-unsaved
// import has to be visible when its dependents are analysed, which is the whole
// reason the build reads through an overlay.
pub fun overlay(st: server-state): _ list<(path, vfile)>
  st.docs.map(fn(o) (o.uri.uri-to-path, Vfile(o.text, o.mtime)))
