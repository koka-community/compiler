fun xs(l: list<list<int>>)
  l

fun program/pretty(Program(_, n, _, typeDefs, defs, imports, externals, fixDefs, _):userProgram): div doc
  vcat(Cons("module".text |+| n.pretty, imports.map(fn(i) i.pretty) ++ fixDefs.map(fn(fd) fd.pretty) ++ externals.map(fn(e) e.pretty) ++ typeDefs.map(fn(td) td.pretty) ++ defs.map(fn(d) d.pretty)))
