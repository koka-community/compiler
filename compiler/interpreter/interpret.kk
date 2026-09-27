// Port of src/Interpreter/Interpret.hs -- the REPL loop.
//
// Input goes through isocline (compiler/lib/isocline.kk), the same C library
// upstream reaches via the Haskell `isocline` package. `ic_readline` blocks and
// owns the terminal, so it runs under `compute` on a libuv worker thread and
// the event loop stays free; that is what lets a future `:l` run compilation
// concurrently and interrupt it with `isocline/async-stop`.
//
// Not yet wired: the expression family (Eval/TypeOf/KindOf/Define/TypeDef).
// Upstream routes those through `buildcCompileExpr`, which builds a VIRTUAL
// `@main.kk` module over an in-memory VFS -- machinery this port does not have
// (`Compile/BuildContext.hs`'s `withVirtualModule`/`withVirtualFile` and
// `Build.hs`'s `vfs*`). They report that rather than pretending to work.
module compiler/interpreter/interpret

import std/os/path
import std/os/dir
import std/os/env
import std/os/process
import std/async
import std/async/thread
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/parse
import std/core/undiv
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/isocline
import compiler/platform/config
import compiler/compile/options
import compiler/compile/build
import compiler/compile/build-context
import compiler/compile/link
import compiler/compile/vfs
import compiler/type/type
import compiler/type/pretty
import compiler/type/assumption
import compiler/kind/synonyms
import compiler/kind/assumption
import compiler/kind/pretty
import compiler/interpreter/command

// upstream `State`; the fields this port does not use yet (printer, defines,
// evalDisable) are omitted rather than carried dead.
struct istate
  flags: flags
  last-load: list<string>
  module-name: name
  // Carried across commands so an expression can be compiled against what was
  // loaded: the resolved build state, the modules to `@open import`, and the
  // directory they came from (added to the include path so the synthetic
  // `@main` module can resolve them).
  sess: session = Session()
  roots: list<name> = []
  root-dir: string = "."
  // captured from the last load, for the listing commands (upstream reads these
  // out of its build context via `buildcGetDefinitions`)
  gam: gamma = gamma/new([])
  syns: synonyms = synonyms/empty
  kgam: kGamma = kgamma/empty

pub fun interpret(fl0: flags, files: list<string>): _ ()
  val bdir = fl0.buildDir
  with with-readline(bdir)
  message-header()
  val st0 = Istate(fl0, [], "".new-name)
  // upstream loads std/core first so the standard functions are in scope; the
  // port has no persistent build context yet, so there is nothing to preload.
  val st1 = match files
    Nil -> st0
    _ -> do-command(st0, Load(files, False))
  loop(st1)

fun loop(st: istate): _ ()
  match get-command(st)
    Nothing -> ()                       // EOF (ctrl-D) or interrupted
    Just(Quit) -> ()
    Just(cmd) -> loop(do-command(st, cmd))

// Read a line and parse it
fun get-command(st: istate): _ maybe<command>
  val p = prompt(st)
  match compute({ isocline/readline(p) })
    Nothing ->
      println("")
      Nothing
    Just(line) ->
      if !line.trim.is-empty then history-add(line)
      Just(line.read-command)

fun prompt(^st: istate): string
  "> "

fun do-command(st: istate, cmd: command): _ istate
  match cmd
    CmdNone -> st
    Quit -> st
    CmdError(msg) ->
      println(msg)
      println("(type \":?\" for help on commands)")
      st
    CmdShow(ShowHelp) ->
      show-help(st)
      st
    CmdShow(ShowVersion) ->
      show-version()
      st
    ChangeDir(d) ->
      // upstream also CHANGES directory; std/os has `cwd()` but no chdir, so
      // only the query half is available here
      if d.is-empty then println(cwd().string)
      else not-wired("changing directory (std/os has no chdir)")
      st
    Shell(c) ->
      run-shell(c)
      println("")
      st
    Options(opts) -> set-options(st, opts)
    Load(fnames, force) ->
      val st1 = st(last-load = fnames)
      load-modules(st1, fnames, force)
    Reload -> load-modules(st, st.last-load, False)
    // Hand the file to $EDITOR (it also jumps to the last
    // error location; this port opens the file and leaves it there)
    Edit(f) ->
      val target = if f.is-empty then st.last-load.head.default("") else f
      if target.is-empty then println("nothing to edit")
      else
        val ed = get-env-value("EDITOR").default("")
        if ed.is-empty then println("set the EDITOR environment variable to use :edit")
        else
          match run-system-read(ed ++ " " ++ target)
            Ok(out) -> print(out)
            Error(e) -> println("could not run editor: " ++ e.message)
      st
    // the expression family (upstream `buildRunExpr` / `buildTypeExpr`)
    Eval(line) -> st.run-expr(line)
    TypeOf(line) -> st.type-expr(line)
    KindOf(_) ->
      not-wired(":kind <type>")
      st
    Define(_) ->
      not-wired("interactive definitions")
      st
    TypeDef(_) ->
      not-wired("interactive type definitions")
      st
    // List what the loaded modules define
    CmdShow(ShowTypeSigs) ->
      with with-pretty-env
      if st.gam.assumption/list.is-nil then println("no types to show")
      else println(st.gam.pp-gamma.show)
      st
    CmdShow(ShowKindSigs) ->
      with with-pretty-env
      println(st.kgam.pp-kgamma(st.module-name).show)
      st
    CmdShow(ShowSynonyms) ->
      with with-pretty-env
      println(st.syns.pp-synonyms.show)
      st
    CmdShow(_) ->
      not-wired("that :show command")
      st

fun not-wired(what: string): <io> ()
  println("not yet supported in this port: " ++ what)

fun load-modules(st: istate, files: list<string>, force: bool): _ istate
  if files.is-nil then
    println("nothing to load")
    st
  else
    val fl0 = st.flags
    val fl = if force then fl0(rebuild = True) else fl0
    // remember what was loaded so an expression can import it
    val mods : ref<global,list<name>> = ref([])
    val sess : ref<global,session> = ref(st.sess)
    val defs : ref<global,maybe<(gamma, synonyms, kGamma)>> = ref(Nothing)
    files.foreach fn(f)
      println("loading: " ++ f)
      compile-one(fl, f, mods, sess, defs)
      // clear the in-place progress line
      print("\r" ++ " ".repeat(60) ++ "\r")
    val dir = match files.head
      Just(f) -> f.path.dirname.show
      Nothing -> st.root-dir
    val st1 = st(sess = !sess, roots = !mods, root-dir = if dir.is-empty then "." else dir)
    match !defs
      Just((g, sy, kg)) -> st1(gam = g, syns = sy, kgam = kg)
      Nothing -> st1

// the same error/warning plumbing driver.kk's `compile-files` installs around
// a single compile, so a REPL load reports exactly like a batch compile
fun compile-one(fl: flags, fname: string, mods: ref<global,list<name>>, sess: ref<global,session>,
                defs: ref<global,maybe<(gamma, synonyms, kGamma)>>): _ ()
  var warnings : warnings := []
  fun flush-warnings()
    warnings.foreach fn(e) println(e.err/show)
    warnings := []
  with handler
    final ctl parse-error(e: string, r: range)
      println(r.show ++ ": parse error: " ++ e)
      flush-warnings()
      ()
  with collapse-div
  with handler
    final ctl add-errors(errs: errors)
      errs.take(fl.maxErrors).foreach fn(e) println(e.err/show)
      flush-warnings()
      ()
    fun add-warnings(warns: warnings)
      warnings := warnings ++ warns
    fun add-infos(infos: warnings)
      warnings := warnings ++ infos
  // Live progress. The orchestrator invokes this on ITS strand as each module
  // finishes, and `ic_readline` is not holding the terminal here, so an
  // in-place `\r` line is safe. Compilation itself runs on worker threads, so
  // this costs the build nothing.
  fun report(done: int, total: int, m: name)
    print("\r  [" ++ done.show ++ "/" ++ total.show ++ "] " ++ m.show-plain.pad-right(40).first(40).string)
  fun capture(ModuleCheck(nm, _rm, g, _pr, _nt, sy, kg): module-check)
    mods.set((!mods ++ [nm]).distinct-names)
    defs.set(Just((g, sy, kg)))
  match try({check-file-session(fl, fname, !sess, on-progress = report, on-range-map = capture)})
    Error(exn) -> println(exn.message)
    Ok(s2) -> sess.set(s2)
  flush-warnings()

fun distinct-names(ns: list<name>): list<name>
  ns.foldl([], fn(acc, n) if acc.any(fn(m) m == n) then acc else acc ++ [n])

fun set-options(st: istate, opts: string): _ istate
  match parse-options(st.flags, opts.unquote)
    Left(msg) ->
      println(msg)
      st
    Right((fl, _)) -> st(flags = fl)

//----------------------------------------------------------------------
// messages (upstream's message* family, plain for now -- the port has no
// ColorPrinter-backed terminal in the interpreter yet)
//----------------------------------------------------------------------

fun message-header(): <io,comp-flags> ()
  println("Koka " ++ comp-flags.version ++ " (self-hosted port), :? for help")

fun show-version(): <io,comp-flags> ()
  println("Koka " ++ comp-flags.version)

fun show-help(^st: istate): <io> ()
  println(command-help(ColorScheme()).show)

// upstream runs the command through the shell
fun run-shell(c: string): <io> ()
  process/run-system(c).ignore


//----------------------------------------------------------------------
// the expression family
//----------------------------------------------------------------------

// Compile `line` as an expression against what is loaded. `check` selects
// upstream's `buildTypeExpr` (type only) or `buildRunExpr` (build and run).
fun with-expr(st: istate, line: string, check-only: bool): _ (istate, maybe<ktype>, maybe<path>)
  if st.roots.is-nil then
    println("nothing loaded; use `:l <file>` first")
    (st, Nothing, Nothing)
  else
    // the loaded file's own directory must be searchable, since the synthetic
    // module lives under the virtual mount and imports the roots by name
    val fl0 = st.flags
    val fl = fl0(includePath = fl0.includePath ++ [st.root-dir])
    var out : (istate, maybe<ktype>, maybe<path>) := (st, Nothing, Nothing)
    fun go(): _ ()
      with handler
        final ctl parse-error(e: string, r: range)
          println(r.show ++ ": parse error: " ++ e)
          ()
      with collapse-div
      with handler
        final ctl add-errors(errs: errors)
          errs.take(fl.maxErrors).foreach(fn(e) println(e.err/show))
          ()
        fun add-warnings(w: warnings) w.foreach(fn(e) println(e.err/show))
        fun add-infos(w: warnings) w.foreach(fn(e) println(e.err/show))
      match try({ compile-expr(fl, st.sess, line, st.roots, "", type-check-only = check-only) })
        Error(exn) -> println(exn.message)
        Ok(Expr-result(s2, tp, exe)) -> out := (st(sess = s2), tp, exe)
    go()
    out

fun type-expr(st: istate, line: string): _ istate
  val (st1, tp, _) = st.with-expr(line, True)
  match tp
    Just(t) ->
      with with-pretty-env
      println(line ++ " : " ++ t.ktp/pretty-string)
    Nothing -> ()
  st1

fun run-expr(st: istate, line: string): _ istate
  val (st1, _, exe) = st.with-expr(line, False)
  match exe
    Just(p) ->
      val (out, _code) = run-exe(p, st.flags.execOpts)
      print(out)
    Nothing -> ()
  st1
