pub inline extern replace-all( s : string, pattern : string, repl : string ) : string
  c  "kk_string_replace_all"
  cs inline "(#1).Replace(#2,#3)"
  js inline r"(#1).replace(new RegExp((#2).replace(/[\\\$\^*+\-{}?().]/g,'\\$&'),'g'),#3)"

// Count occurrences of `pattern` in a string.
pub inline extern stringpat/count( s : string, pattern : string ) : int
  c  "kk_string_count_pattern"
  cs inline "Primitive.Count(#1,#2)"
  js inline r"((#2) ? ((#1).match(new RegExp((#2).replace(/[\\\$\^*+\-{}?().]/g,'\\$&'),'g'))||[]).length : 0)"

