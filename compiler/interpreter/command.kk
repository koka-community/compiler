// Port of src/Interpreter/Command.hs -- the REPL command grammar.
//
// Upstream parses with Parsec; the grammar is a single line of the form
// `:cmd args` or a bare expression, so this is hand-rolled over the string
// instead. The lexical rules it reproduces are upstream's:
//   * `symbol n`  -- case-insensitive `n` NOT followed by an alphanumeric,
//                    then trailing whitespace (so `:l` and `:load` are
//                    distinct, and `:loadx` is neither)
//   * `special n` -- exact `n`, then trailing whitespace
//   * `anything`  -- the rest of the line
//
// Constructors are renamed where the upstream name is taken in Koka:
// `Error`/`None`/`Show` become `CmdError`/`CmdNone`/`CmdShow`.
module compiler/interpreter/command

import compiler/common/color-scheme
import compiler/lib/pprint

pub type command
  Quit
  CmdError(msg: string)
  Load(paths: list<string>, force: bool)   // force = rebuild everything (`:f`)
  Reload
  Eval(src: string)
  TypeOf(src: string)
  KindOf(src: string)
  Define(src: string)
  TypeDef(src: string)
  Options(opts: string)
  Edit(path: string)
  Shell(cmd: string)
  ChangeDir(path: string)
  CmdShow(scmd: show-command)
  CmdNone

pub type show-command
  ShowSource
  ShowTypeSigs
  ShowKindSigs
  ShowSynonyms
  ShowDefines
  ShowHelp
  ShowVersion

pub fun read-command(line: string): div command
  parse-command(line.edit-backspaces)

// Apply backspaces in the raw line before parsing
fun edit-backspaces(s: string): string
  val out = s.list.foldl([]) fn(acc, c)
    if c == '\x08' then match acc { Cons(_, rest) -> rest; Nil -> [] }
    else Cons(c, acc)
  out.reverse.string

fun parse-command(input: string): div command
  val rest = input.skip-white
  if rest.is-empty then CmdNone
  else match rest.try-special(":")
    // once `:` is consumed upstream's `<|>` cannot backtrack either, so an
    // unknown command is an error rather than falling through to `expression`
    Just(r) -> cmd-eval(input, r)
    Nothing -> expression(rest)

fun cmd-eval(input: string, r0: string): div command
  match [("l", False), ("load", False), ("f", True), ("fload", True)].first-symbol(r0)
    Just((force, r)) -> return Load(r.filenames, force)
    Nothing -> ()
  match ["r", "reload"].any-symbol(r0)
    Just -> return Reload
    Nothing -> ()
  match ["q", "quit"].any-symbol(r0)
    Just -> return Quit
    Nothing -> ()
  match ["e", "edit"].any-symbol(r0)
    Just(r) -> return Edit(r.filenames.head.default(""))
    Nothing -> ()
  match ["cd"].any-symbol(r0)
    Just(r) -> return ChangeDir(r.filenames.head.default(""))
    Nothing -> ()
  match r0.try-special("!")
    Just(r) -> return Shell(r.anything)
    Nothing -> ()
  match r0.try-special("?")
    Just -> return CmdShow(ShowHelp)
    Nothing -> ()
  match ["h", "help"].any-symbol(r0)
    Just -> return CmdShow(ShowHelp)
    Nothing -> ()
  // `:t` alone lists the signatures in scope; `:t <expr>` types the
  // expression. The expression is padded to its ORIGINAL column so error
  // positions still line up with what the user typed (upstream
  // `replicate (sourceColumn p - 1) ' '`).
  match ["t", "type", "b", "browse"].any-symbol(r0)
    Just(r) -> return (if r.is-empty then CmdShow(ShowTypeSigs) else TypeOf(pad-to-column(input, r)))
    Nothing -> ()
  match ["k", "kind"].any-symbol(r0)
    Just(r) -> return (if r.is-empty then CmdShow(ShowKindSigs) else KindOf(pad-to-column(input, r)))
    Nothing -> ()
  match ["set"].any-symbol(r0)
    Just(r) -> return Options(r.command-line)
    Nothing -> ()
  match ["s", "source"].any-symbol(r0)
    Just -> return CmdShow(ShowSource)
    Nothing -> ()
  match ["d", "defines"].any-symbol(r0)
    Just -> return CmdShow(ShowDefines)
    Nothing -> ()
  match ["alias"].any-symbol(r0)
    Just -> return CmdShow(ShowSynonyms)
    Nothing -> ()
  match ["w", "warranty", "version"].any-symbol(r0)
    Just -> return CmdShow(ShowVersion)
    Nothing -> ()
  CmdError("error in command: expecting command")

// Classify a bare line by its leading keyword
fun expression(src0: string): command
  val src = src0.anything
  if src.is-empty then CmdNone
  elif src.starts-with-str("fun") || src.starts-with-str("val") then Define(src)
  elif ["type", "open type", "extend type", "co type", "div type", "alias", "struct"]
         .any(fn(d) src.starts-with-str(d)) then TypeDef(src)
  else Eval(src)

//----------------------------------------------------------------------
// lexical helpers (upstream's `lexeme`/`symbol`/`special`/`filename`)
//----------------------------------------------------------------------

fun skip-white(s: string): string
  s.list.drop-while(is-white).string

fun starts-with-str(s: string, pre: string): bool
  s.starts-with(pre).bool

// Case-insensitive, not followed by an alphanumeric
fun try-symbol(s: string, name: string): maybe<string>
  val cs = s.list
  val ns = name.to-lower.list
  if cs.length < ns.length then Nothing
  elif !cs.take(ns.length).map(char/to-lower).zip(ns).all(fn((a, b)) a == b) then Nothing
  else
    val rest = cs.drop(ns.length)
    match rest
      Cons(c) | c.is-alpha-num -> Nothing
      _ -> Just(rest.string.skip-white)

fun any-symbol(names: list<string>, s: string): maybe<string>
  names.foldl(Nothing) fn(acc, n) match acc { Just -> acc; Nothing -> s.try-symbol(n) }

fun first-symbol(alts: list<(string, a)>, s: string): maybe<(a, string)>
  alts.foldl(Nothing) fn(acc, (n, v))
    match acc
      Just -> acc
      Nothing -> match s.try-symbol(n) { Just(r) -> Just((v, r)); Nothing -> Nothing }

// Exact match, then whitespace
fun try-special(s: string, name: string): maybe<string>
  if s.starts-with-str(name) then Just(s.list.drop(name.count).string.skip-white) else Nothing

// The rest of the line, then trailing whitespace
fun anything(s: string): string
  s.trim-right

// Everything up to a newline
fun command-line(s: string): string
  s.list.take-while(fn(c) c != '\n').string

// upstream `filenames`/`filename`: a quoted string, or a run of characters
// that are neither whitespace nor a quote
fun filenames(s: string): div list<string>
  val r = s.skip-white
  if r.is-empty then []
  else
    val (f, rest) = r.filename
    if f.is-empty then [] else Cons(f, rest.filenames)

fun filename(s: string): (string, string)
  match s.list
    Cons('"', cs) ->
      val f = cs.take-while(fn(c) c != '"' && c != '\n')
      (f.string, cs.drop(f.length + 1).string)
    cs ->
      val f = cs.take-while(fn(c) c != '"' && c != '\n' && !c.is-white)
      (f.string, cs.drop(f.length).string)

// how many characters of `input` were consumed before `rest` begins
fun pad-to-column(input: string, rest: string): string
  " ".repeat(input.count - rest.count) ++ rest.anything

//----------------------------------------------------------------------

pub fun command-help(colors: colorScheme): doc
  fun infotext(s: string): doc
    s.text.color(colors.colorInterpreter)
  fun cmd(c: string, arg: string, explain: string): doc
    c.text.fill(12) |.| arg.text.fill(14) |.| infotext(explain)
  (infotext("commands:") |-| [
    cmd("<expression>", "", "evaluate the given expression"),
    cmd(":l[oad]", "{modulename}", "load module(s)"),
    cmd(":f[load]", "{modulename}", "force load module(s) rebuilding everything"),
    cmd(":r[eload]", "", "reload the current module(s)"),
    cmd(":e[dit]", "[filename]", "edit file (and jump to error location)"),
    cmd(":set", "<options>", "set (command line) options"),
    pprint/empty,
    cmd(":t[ype]", "[expression]", "show type signature(s) (of a given expression)"),
    cmd(":k[ind]", "", "show kind signatures in scope"),
    cmd(":alias", "", "show type alias signatures"),
    cmd(":version", "", "show version and warranty information"),
    cmd(":cd", "", "show the current directory"),
    cmd(":cd", "<directory>", "change the current directory"),
    cmd(":!", "<command>", "run a shell command"),
    cmd(":?", "", "show this information"),
    cmd(":q[uit]", "", "quit the interpreter"),
    pprint/empty
  ].vcat).hang(2) |-|
  (infotext("remarks:") |-| ["Use :set -? to see help on command line flags.".text].vcat).hang(2)
