# The Yacc/Flex specification of the Koka grammar.

You can compile and run these as:

```
$ stack exec koka -- -e util/grammar.kk
```

This writes output to `.koka/grammar` including 
the file `.koka/grammar/parser.output` which can be used
to resolve parse conflicts.

Uses the `CC` environment variable to determine the C compiler.

Assumes `bison` and `flex` are installed.
- On Linux, use `sudo apt install bison flex`. 
- Requires at least Flex 2.5.37; you can get a version for windows from:
  <https://sourceforge.net/projects/winflexbison>
- Requires at least Bison 3+; you can get a version for windows from:
  <https://sourceforge.net/projects/winflexbison> (use the "latest" zip package)