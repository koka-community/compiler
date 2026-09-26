{
import compiler/common/name
import compiler/common/range
import compiler/syntax/lexeme
import std/core/bslice
import std/num/float64
import std/core-extras
import std/core/undiv
import std/data/word-set
import std/data/trie
// Updated to be roughly equivalent to commit dd910825 on 7/23/26

pub effect koka-lex
  fun do-start-chunked(s: string, start: alex-pos, content-off: int): ()
  fun end-chunked(): (string, alex-pos)
  // Extend the open chunk over the matched SPAN of the input. Both offsets are
  // passed so the handler can tell whether this match continues the span it is
  // already holding; a non-contiguous match (nested block comments can produce
  // one) materialises what it has and starts a fresh span. Nothing is copied
  // per match -- the text is sliced once when the chunk is finalised.
  fun extend-chunk(start-off: int, end-off: int): ()
  fun get-rawdelim(): int
  fun set-rawdelim(i: int): ()
  fun check-linedir(c: lex, start: alex-pos, end: alex-pos): lex
  fun do-emit(l: lex, start: alex-pos, end: alex-pos): ()

fun emit(l: lex): <alex,koka-lex> ()
  do-emit(l, get-start(), get-end())

fun start-chunked(s: string): <alex,koka-lex> ()
  // `s` is the already-matched opening text ("//", "/*", or "" for a string);
  // the chunk's own content starts at the current scan position
  do-start-chunked(s, get-start(), get-end().offset)

fun end-chunk(f: (string) -> <alex,koka-lex> lex): <alex,koka-lex> ()
  val (s, start) = end-chunked()
  do-emit(f(s), start, get-end())
}


%encoding "latin1"
%wrapper "effect"
%effects "koka-lex"

-----------------------------------------------------------
-- Character sets
-----------------------------------------------------------
$digit        = [0-9]
$hexdigit     = [0-9a-fA-F]
$lower        = [a-z]
$upper        = [A-Z]
$letter       = [$lower$upper]
$space        = [\ ]
$tab          = [\t]
$return       = \r
$linefeed     = \n
$graphic      = [\x21-\x7E]
$cont         = [\x80-\xBF]
$symbol       = [\$\%\&\*\+\~\!\\\^\#\=\.\:\-\|\<\>]
$special      = [\(\)\[\]\{\}\;\,\?]
$anglebar     = [\<\>\|]
$angle        = [\<\>]
$finalid      = [\']
$charesc      = [nrt\\\'\"]    -- "

-----------------------------------------------------------
-- Regular expressions
-----------------------------------------------------------
@newline      = $return?$linefeed

@utf8valid    = [\xC2-\xDF] $cont
              | \xE0 [\xA0-\xBF] $cont
              | [\xE1-\xEC] $cont $cont
              | \xED [\x80-\x9F] $cont
              | [\xEE-\xEF] $cont $cont
              | \xF0 [\x90-\xBF] $cont $cont
              | [\xF1-\xF3] $cont $cont $cont
              | \xF4 [\x80-\x8F] $cont $cont

@utf8unsafe   = \xE2 \x80 [\x8E-\x8F\xAA-\xAE]
              | \xE2 \x81 [\xA6-\xA9]

@utf8         = @utf8valid          

@linechar     = [$graphic$space$tab]|@utf8
@commentchar  = ([$graphic$space$tab] # [\/\*])|@newline|@utf8

@hexdigit2    = $hexdigit $hexdigit
@hexdigit4    = @hexdigit2 @hexdigit2
@hexesc       = x@hexdigit2|u@hexdigit4|U@hexdigit4@hexdigit2
@escape       = \\($charesc|@hexesc)
@stringchar   = ([$graphic$space] # [\\\"])|@utf8             -- " fix highlight
@charchar     = ([$graphic$space] # [\\\'])|@utf8
@stringraw    = ([$graphic$space$tab] # [\"])|@newline|@utf8  -- "

@idchar       = $letter | $digit | _ | \- | \@
@lowerid      = [\@]? $lower @idchar* $finalid*
@upperid      = [\@]? $upper @idchar* $finalid*
@wildcard     = [\@]? _ @idchar*
@conid        = @upperid

@modpart      = @lowerid\/
@modulepath   = @modpart+ (\# @modpart*)? | \? @modpart*
@qvarid       = @modulepath @lowerid
@qconid       = @modulepath @conid

@op           = $symbol+ | \/
@idsym        = @lowerid? ($symbol+ | \/)
@qidop        = @modulepath \(@idsym\)
@idop         = \(@idsym\)

@sign         = [\-]?
@digitsep     = _ $digit+
@hexdigitsep  = _ $hexdigit+
@digits       = $digit+ @digitsep*
@hexdigits    = $hexdigit+ @hexdigitsep*
@decimal      = 0 | [1-9] (_? @digits)?
@hexadecimal  = 0[xX] @hexdigits
@integer      = @sign (@decimal | @hexadecimal)

@exp          = (\-|\+)? $digit+
@exp10        = [eE] @exp
@exp2         = [pP] @exp
@decfloat     = @sign @decimal (\. @digits @exp10? | @exp10)
@hexfloat     = @sign @hexadecimal (\. @hexdigits @exp2? | @exp2)

-----------------------------------------------------------
-- Main tokenizer
-----------------------------------------------------------
program :-
-- white space
<0> $space+               { fn() { emit(LexWhite(get-string()))} }
<0> @newline              { fn() { emit(LexWhite("\n")) } }
<0> "/*" $symbol*         { fn() { push-state(comment); start-chunked(get-string()); } }
<0> "//" $symbol*         { fn() { push-state(linecom); start-chunked(get-string()); } }
<0> @newline\# $symbol*   { fn() { push-state(linedir); start-chunked(get-string()); } }


-- qualified identifiers
<0> @qconid               { fn() { emit(LexCons(get-qname(), "")) } }
<0> @qvarid               { fn() { emit(LexId(get-qname())) } }
<0> @qidop                { fn() { emit(LexIdOp(get-qname())) } }

-- identifiers
<0> @lowerid              { fn() {
    val s = get-string();
    if s.is-reserved then emit(LexKeyword(s, ""))
    elif s.is-malformed then emit(LexError(message-malformed))
    else emit(LexId(s.new-name))
  }}
<0> @conid                { fn() { emit(LexCons(get-name(), "")) } }
<0> @wildcard             { fn() { emit(LexWildCard(get-name())) } }

-- specials
<0> $special              { fn() { emit(LexSpecial(get-string())) } }

-- literals
<0> @decfloat             { fn() { val s = get-string(); emit(LexFloat(s.replace-all("_", "").parse-float64.expect("when parsing " ++ s), s)) } }
<0> @hexfloat             { fn() { val s = get-string(); emit(LexFloat(s.replace-all("_", "").parse-float64.expect("when parsing " ++ s), s)) } }
<0> @integer              { fn() { val s = get-string(); emit(LexInt(s.replace-all("_", "").parse-int.expect("when parsing " ++ s), s)) } }


-- type operators
<0> "||"                  { fn() { emit(LexOp(get-name())) } }

-- operators
<0> @idop                 { fn() { emit(LexIdOp(get-qname())) } }
<0> @op                   { fn() {
    val s = get-string();  
    if s.is-reserved then emit(LexKeyword(s,""))
    elif s.is-prefix-op then emit(LexPrefix(s.new-name))
    else s.split-op.foreach(emit)
   }}


-- characters
<0> \"                    { fn() { push-state(stringlit); start-chunked(""); } } -- "
<0> r\#*\"                { fn() { push-state(stringraw); start-chunked(""); push-rawdelim(); } } -- "

<0> \'\\$charesc\'        { fn() { emit(LexChar(get-sslice().sslice/drop(2).next.unjust.tuple2/fst.char/from-char-esc)) }}
<0> \'\\@hexesc\'         { fn() { emit(LexChar(get-sslice().sslice/drop(3).extend(-1).char/from-hex-esc)) }}
<0> \'@charchar\'         { fn() { emit(LexChar(get-sslice().sslice/drop(1).next.unjust.tuple2/fst)) }}
<0> \'.\'                 { fn() { emit(LexError("illegal character literal: " ++ get-sslice().sslice/drop(1).next.map(tuple2/fst).default(' ').show)) }}

-- catch errors
<0> $tab+                 { fn() { emit(LexError("tab characters: configure your editor to use spaces instead (soft tab)")) }}
<0> .                     { fn() { emit(LexError("illegal character: " ++ get-sslice().show ++ (if (get-string() =="\t") then " (replace tabs with spaces)" else ""))) }}

--------------------------
-- string literals

<stringlit> @utf8unsafe   { fn() { unsafe-char("string") } }
<stringlit> @stringchar+  { fn() { extend-span() } }
<stringlit> \\$charesc    { fn() { extend-span() } }
<stringlit> \\@hexesc     { fn() { extend-span() } }
<stringlit> \"            { fn() { pop-state(); end-chunk(fn(s) LexString(s.unescape-string)) } } -- " 
<stringlit> @newline      { fn() { pop-state(); end-chunk(fn(s) LexError("string literal ended by a new line")) } }
<stringlit> .             { fn() { pop-state(); end-chunk(fn(s) LexError("illegal character in string: " ++ s.show)) } }

<stringraw> @utf8unsafe   { fn() { unsafe-char("raw string") } }
<stringraw> @stringraw    { fn() { extend-span() } }
<stringraw> \"\#*         { fn() {
                            val delim = get-sslice().count - 1
                            val curdelim = get-rawdelim()
                            if delim == curdelim then
                              end-chunk(fn(s) LexString(s))
                              pop-state()
                              pop-rawdelim()
                            elif delim > curdelim then // too many terminating hashes
                              emit(LexError("raw string: too many '#' terminators in raw string (expecting " ++ show(delim - 1) ++ ")"))
                              end-chunked()
                              pop-state()
                              pop-rawdelim()
                            else // continue
                              extend-span()
                          }}
<stringraw> .             { fn() {
  end-chunk(fn(s) LexError("illegal character in raw string: " ++ s.show))
  pop-state()
  pop-rawdelim()
 }}


--------------------------
-- block comments

<comment> "*/"            { fn() {
  val st = pop-state()
  // TODO? end-chunked()
  if st == comment then extend-span()
  else
    extend-span() // upstream `withmore`: include the matched "*/" in the comment text
    end-chunk(fn(s) LexComment(s.list.filter(fn(c) c != '\r').string))
    pop-state()
    ()
}}
<comment> "/*"            { fn() { push-state(comment); start-chunked(get-string()); } }
<comment> @utf8unsafe     { fn() { unsafe-char("comment") } }
<comment> @commentchar    { fn() { extend-span() } }
<comment> [\/\*]          { fn() { extend-span() } }
<comment> .               { fn() { pop-state(); end-chunk(fn(s) LexError("illegal character in comment: " ++ s.show)) } }

--------------------------
-- line comments

<linecom> @utf8unsafe     { fn() { unsafe-char("line comment") } }
<linecom> @linechar       { fn() { extend-span() } }
<linecom> @newline        { fn() { pop-state(); extend-span(); end-chunk(fn(s) LexComment(s.list.filter(fn(c) c !='\r').string)) } }
<linecom> .               { fn() { pop-state(); end-chunk(fn(s) LexError("illegal character in line comment: " ++ s.show)) } }

--------------------------
-- line directives (ignored for now)

<linedir> @utf8unsafe     { fn() { unsafe-char("line directive") } }
<linedir> @linechar       { fn() { extend-span() } }
<linedir> @newline        { fn() { pop-state(); extend-span(); end-chunk(fn(s) check-linedir(LexComment(s.list.filter(fn(c) c !='\r').string), get-start(), get-end())) } }
<linedir> .               { fn() { pop-state(); end-chunk(fn(s) LexError("illegal character in line directive: " ++ s.show)) } }

{

fun is-anglebar(c: char): bool
  match c
    '|' -> True
    '<' -> True
    '>' -> True
    _ -> False

fun split-op(s: string): list<lex>
  fun split(s': list<char>): list<lex>
    match s'
      Cons('|', rst) | rst.all(fn(r) r.is-anglebar) -> Cons(LexKeyword("|", ""), split(rst))
      Cons('>', rst) -> Cons(LexOp(">".new-name), split(rst))
      Cons('<', rst) -> Cons(LexOp("<".new-name), split(rst))
      Nil -> Nil
      xs -> Cons(LexOp(xs.string.new-name), Nil)
  val sl = s.list
  if sl.all(fn(c) c.is-anglebar) then // A type operator
    split(sl)
  else Cons(LexOp(s.new-name), Nil)

fun extend-span(): <alex,koka-lex> ()
  extend-chunk(get-start().offset, get-end().offset)

fun pop-rawdelim()
  set-rawdelim(0)

fun push-rawdelim()
  set-rawdelim(get-sslice().count - 2)

fun get-name()
  get-string().new-name

fun get-qname()
  get-string().read-qualified-name

fun unsafe-char(kind: string)
  LexError("unsafe character in " ++ kind ++ ": " ++ get-string())
  end-chunked()
  pop-state()
  ()

fun strip-parens(s: sslice)
  match s.string.list.reverse
    Cons(')', cs) -> 
      match cs.span(fn(c) { c != '(' })
        (op, Cons('(', qual)) -> (op ++ qual).reverse.string
        _ -> s.string
    _ -> s.string


// Reserved
val special-names = [ "{", "}"
    , "(", ")"
    , "<", ">"
    , "[", "]"
    , ";", ","
]
// A fixed keyword set: build it as a PURE IMMUTABLE trie. It used to be a
// lazy `delay` around `string-pool()`, whose named handler closes over a
// mutable `var trie`. Forcing a lazy thunk mutates it, and each parallel
// worker gets its own Koka heap/refcount domain, so two workers forcing this
// concurrently is a use-after-free (EXC_BAD_ACCESS in tuple2_unbox, with
// another thread inside kk_block_fast_drop_free). Nothing here needs
// interning or laziness.
// the same words as `reserved-names`, as a LIST: a `word-set` cannot be
// enumerated, and the language server offers keyword completions from it
pub val reserved-name-list : list<string> =
        ["infix", "infixr", "infixl"
              , "module", "import", "as"
              , "pub", "abstract"
              , "type", "alias", "effect", "struct", "con"
              , "forall", "exists", "some"
              , "fun", "fn", "val", "var", "extern"
              , "if", "then", "else", "elif"
              , "match", "return", "with", "in"
              , "handle", "handler", "mask"
              , "ctl", "final", "raw"
              , "override", "named"
              , "ctx", "hole"

              // deprecated
              , "private", "public"  // use pub
              , "rawctl", "brk"      // use raw ctl, and final ctl
              , "prefix", "postfix"

              // alternative names for backwards paper compatability
              , "control", "rcontrol", "except"
              , "ambient", "context" // use effcet
              , "inject"       // use mask
              , "use", "using" // use with instead
              , "function"     // use fun
              , "instance"     // use named

              // future reserved
              , "interface"
              , "unsafe"
              , "break"
              , "continue"

              // operators
              , "="
              , "."
              , ":"
              , "->"
              , "<-"
              , ":="
              , "|"]

pub val reserved-names : word-set =
        reserved-name-list.foldl(empty-word-set(), fn(t, w) t.add(w))

fun is-reserved(name: string)
  reserved-names.contains(name)

fun is-prefix-op(name: string)
  name == "!" || name == "~"

fun string/is-malformed(name: string)
  name.list.charlist/is-malformed

fun is-at(c: char): bool
  c == '@'

// TODO: is-letter 
fun charlist/is-malformed(name: list<char>)
  match name
    // @ signs are added postpend to unique names (e.g. "x-@1") for variable x monadic lifted in a function (-).
    Cons('-', Cons(c, cs)) -> !(c.is-alpha || c.is-at) || cs.is-malformed 
    Cons(c, Cons('-', cs)) -> !(c.is-alpha || c.is-digit) || cs.is-malformed
    Cons(_, cs) -> cs.is-malformed
    Nil -> False

val message-malformed
  = "malformed identifier: a dash must be preceded by a letter or digit, and followed by a letter"

fun char/from-char-esc(c)
  match c
    'n' -> '\n'
    'r' -> '\r'
    't' -> '\t'
    _ -> c

// Decode a string literal's escapes over the WHOLE text, once, when the chunk is
// finalised. Escapes used to be decoded per match, which forced every chunk to
// be a transformed slice and so forced the accumulate-and-copy shape; with this
// at the end, every chunk in every state is a plain span of the input.
fun unescape-string(s: string): string
  fun hexval(cs: list<char>, n: int, acc: int): (int, list<char>)
    if n <= 0 then (acc, cs)
    else match cs
      Cons(c, rest) -> hexval(rest.pretend-decreasing, n - 1, acc * 16 + hex-digit-val(c.int))
      Nil -> (acc, Nil)
  fun go(cs: list<char>, acc: list<char>): list<char>
    match cs
      Nil -> acc.reverse
      Cons('\\', Cons(c, rest)) ->
        match c
          'x' ->
            val (v, r) = hexval(rest, 2, 0)
            go(r.pretend-decreasing, Cons(v.char, acc))
          'u' ->
            val (v, r) = hexval(rest, 4, 0)
            go(r.pretend-decreasing, Cons(v.char, acc))
          'U' ->
            val (v, r) = hexval(rest, 6, 0)
            go(r.pretend-decreasing, Cons(v.char, acc))
          _ -> go(rest.pretend-decreasing, Cons(char/from-char-esc(c), acc))
      Cons(c, rest) -> go(rest.pretend-decreasing, Cons(c, acc))
  go(s.list, []).string

fun bslice/from-char-esc(s: bslice): bslice
  // s is the matched `\<c>`; skip the backslash, decode the escape to the actual
  // character, and return it as a fresh single-char byte slice. (Previously this
  // returned the raw `\c` bytes, so string escapes were never decoded.)
  match s.next
    Just2(_, rest) -> match rest.next
      Just2(code, _) -> slice(string/bytes(char/string(char/from-char-esc(int/char(code)))))
      Nothing2 -> s
    Nothing2 -> s

fun hex-digit-val(c: int): int
  if c >= 0x30 && c <= 0x39 then c - 0x30      // 0-9
  elif c >= 0x41 && c <= 0x46 then c - 55      // A-F -> 10..15
  elif c >= 0x61 && c <= 0x66 then c - 87      // a-f -> 10..15
  else 0

// `s` is a slice over the hex digits of a `\xNN` / `\uNNNN` / `\UNNNNNN` escape
fun char/from-hex-esc(s: sslice)
  match s.string.parse-int(hex = True)
    Just(code) -> int/char(code)
    Nothing -> '\n'

// `s` is the matched `\<x|u|U><hexdigits>`; skip the backslash and prefix char,
// fold the remaining hex digits into a codepoint, and return its UTF-8 bytes.
fun bslice/from-hex-esc(s: bslice): bslice
  fun go(sl: bslice, acc: int): int
    match sl.next
      Just2(c, rest) -> go(rest.pretend-decreasing, acc * 16 + hex-digit-val(c))
      Nothing2 -> acc
  val code = match s.next
    Just2(_, r1) -> match r1.next
      Just2(_, r2) -> go(r2, 0)
      Nothing2 -> 0
    Nothing2 -> 0
  slice(string/bytes(char/string(int/char(code))))

}