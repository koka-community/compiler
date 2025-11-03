{
import compiler/common/name
import compiler/common/range
import compiler/syntax/lexeme
import compiler/syntax/old/lex-help
import std/num/float64
import std/core-extras
import std/core/undiv
import std/data/word-set

alias alexInput = state
alias alexUser = ()
fun alexGetByte(s: alexInput): maybe<(char, alexInput)>
  match s.current.next()
    Nothing -> Nothing
    Just((c, s')) -> Just((c, s(current=s')))

fun alexInputPrevChar(s: alexInput): char
  s.previous

}

%encoding "utf8"

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
$symbol       = [\$\%\&\*\+\~\!\\\^\#\=\.\:\-\?\|\<\>]
$special      = [\(\)\[\]\{\}\;\,]
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

@idchar       = $letter | $digit | _ | \-
@lowerid      = $lower @idchar* $finalid*
@upperid      = $upper @idchar* $finalid*
@conid        = @upperid
@modulepath   = (@lowerid\/)+
@qvarid       = @modulepath @lowerid
@qconid       = @modulepath @conid
@symbols      = $symbol+ | \/
@qidop        = @modulepath \(@symbols\)
@idop         = \(@symbols\)

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
<0> $space+               { lex/string(LexWhite) }
<0> @newline              { lex/string(fn(_: string) LexWhite("\n")) }
<0> "/*" $symbol*         { lex/next(comment, more(id)) }
<0> "//" $symbol*         { lex/next(linecom, more(id)) }
<0> @newline\# $symbol*   { lex/next(linedir, more(id)) }


-- qualified identifiers
<0> @qconid               { lex/string(LexCons(_.newQName)) }
<0> @qvarid               { lex/string(LexId(_.newQName)) }
<0> @qidop                { token(LexIdOp(_.strip-parens.newQName)) }

-- identifiers
<0> @lowerid              { lex/string(fn(s: string) {
    if s.is-reserved then LexKeyword(s, "")
    elif s.is-malformed then LexError(message-malformed)
    else LexId(s.new-name)
  }) }
<0> @conid                { lex/string(LexCons(_.new-name)) }
<0> _@idchar*             { lex/string(LexWildCard(_.new-name)) }

-- specials
<0> $special              { lex/string(LexSpecial) }

-- literals
<0> @decfloat             { lex/string(fn(s: string) LexFloat(s.parse-float64.unjust, s)) }
<0> @hexfloat             { lex/string(fn(s: string) LexFloat(s.parse-float64.unjust, s)) }
<0> @integer              { lex/string(fn(s: string) LexInt(s.parse-int.unjust, s)) }


-- type operators
<0> "||"                  { lex/string(LexOp(_.new-name)) }
<0> $anglebar $anglebar+  { less(1, string(fn(s) if (s=="|") then LexKeyword(s, "") else LexOp(s.new-name))) }

-- operators
<0> @idop                 { token(LexIdOp(_.strip-parens.new-name)) }
<0> @symbols              { lex/string(fn(s: string) {    
    if s.is-reserved then LexKeyword(s,"")
    elif s.is-prefix-op then LexPrefix(s.new-name)
    else LexOp(s.new-name)
  }) }


-- characters
<0> \"                    { lex/next(stringlit, more(fn(_) "".slice)) }  -- "
<0> r\#*\"                { lex/next(stringraw, raw-delim(more(fn(_) "".slice))) }  -- "

<0> \'\\$charesc\'        { token(LexChar(_.sslice/drop(2).next.unjust.tuple2/fst.char/from-char-esc)) }
<0> \'\\@hexesc\'         { token(LexChar(_.sslice/drop(3).extend(-1).char/from-hex-esc)) }
<0> \'@charchar\'         { token(LexChar(_.sslice/drop(1).next.unjust.tuple2/fst)) }
<0> \'.\'                 { token(LexError("illegal character literal: " ++ _.sslice/drop(1).next.map(tuple2/fst).default(' ').show)) }

-- catch errors
<0> $tab+                 { token(fn(s:sslice) LexError("tab characters: configure your editor to use spaces instead (soft tab)")) }
<0> .                     { string(fn(s:string) LexError("illegal character: " ++ s.show ++ (if (s=="\t") then " (replace tabs with spaces)" else ""))) }

--------------------------
-- string literals

<stringlit> @utf8unsafe   { string(unsafe-char("string", _)) }
<stringlit> @stringchar   { more(id) }
<stringlit> \\$charesc    { more(sslice/from-char-esc) }
<stringlit> \\@hexesc     { more(sslice/from-hex-esc) }
<stringlit> \"            { pop(fn(_) withmore(token(LexString(_.extend(-1).string)))) } -- "
<stringlit> @newline      { pop(fn(_) token(fn(_) LexError("string literal ended by a new line"))) }
<stringlit> .             { token(LexError("illegal character in string: " ++ _.show)) }

<stringraw> @utf8unsafe   { lex/string(unsafe-char("raw string", _)) }
<stringraw> @stringraw    { more(id) }
<stringraw> \"\#*         { with-raw-delim(fn(s:string, delim:string) {
                              if (s == delim) then  //  done
                                pop(fn(_) less(delim.count, withmore(token(LexString(_.extend(0 - delim.count).string)))))                              
                              elif (s.count > delim.count) then  // too many terminating hashes
                                token(fn(s') LexError("raw string: too many '#' terminators in raw string (expecting " ++ show(delim.count - 1) ++ ")"))
                              else // continue
                                 more(id)
                              }
                            ) 
                          }
<stringraw> .             { token(LexError("illegal character in raw string: " ++ _.show)) }


--------------------------
-- block comments

<comment> "*/"            { 
  pop(fn(state: int) { 
    if state == comment then more(id)
    else withmore(token(LexComment(_.string.list.filter(_ != '\r').string))) 
} ) }
<comment> "/*"            { push(more(id)) }
<comment> @utf8unsafe     { lex/string(unsafe-char("comment", _)) }
<comment> @commentchar    { more(id) }
<comment> [\/\*]          { more(id) }
<comment> .               { token(LexError("illegal character in comment: " ++ _.show)) }

--------------------------
-- line comments

<linecom> @utf8unsafe     { lex/string(unsafe-char("line comment", _)) }
<linecom> @linechar       { more(id) }
<linecom> @newline        { pop(fn(_) {
      withmore(string(fn(s:string) LexComment(s.list.filter(_ !='\r').string)))
    }) 
 }
<linecom> .               { lex/string(LexError("illegal character in line comment: " ++ _.show)) }

--------------------------
-- line directives (ignored for now)

<linedir> @utf8unsafe     { lex/string(unsafe-char("line directive", _)) }
<linedir> @linechar       { more(id) }
<linedir> @newline        { pop(fn(_) withmore(string(LexComment(_.list.filter(_ !='\r').string)))) }
<linedir> .               { lex/string(LexError("illegal character in line directive: " ++ _.show)) }

-- TODO: Add helper functions

{
}