fun xs(l: list<list<int>>)
  l

fun program/pretty(Program(_, n, _, typedefs, defs, imports, externals, fix-defs, _):user-program): div doc
  vcat(Cons("module".text |+| n.pretty, imports.map(fn(i) i.pretty) ++ fix-defs.map(fn(fd) fd.pretty) ++ externals.map(fn(e) e.pretty) ++ typedefs.map(fn(td) td.pretty) ++ defs.map(fn(d) d.pretty)))
