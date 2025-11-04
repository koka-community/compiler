# TODO
Work on Syntax, Parsing, and Formatter

## Fully up to date
// syntax / highlight 11/11/24

- [x] lib/ updated: 2/10/25
- [x] common/ updated: 11/3/25 (except file)
- [x] syntax/ updated 7/14/25 (pretty, format are new)
- [x] static/ updated 7/12/25 
- [ ] kind/ updated 7/12/25 (other than kind/infer..lazy)
- [ ] type/type, type/kind type/operations, type/pretty, updated 1/8/25, assumption possibly updated to 7/14/25
- [ ] syntax/ needs debugging / tests

## 
Notes:
- move common/parser to std/text/parser
- move error / partial results to general error handling 

Small missing
- [ ] syntax/highlight 11/11/24 - partial (missing isocline?)
- [ ] common/range - some missing
- [ ] common/file - some missing

## Changes
https://github.com/koka-lang/koka/compare/46b4fe631df398940727febc2a4f278da938842e...dev
- [ ] type/typevar
- [ ] type/infgamma
- [ ] type/assumption
- [ ] type/unify
- [ ] core/*
- [ ] backend/c/*

## All dependencies ready
- [ ] backend/c/parc 1037
- [ ] backend/c/parcreuse 731
- [ ] backend/c/parcreusespec 341
- [ ] core/ctail 691
- [ ] core/simplify 970
- [ ] syntax/highlight 515 - needs isocline

## Next priority (lots of dependencies require)

## Needs dependencies
- [ ] core/analysismatch 248 - needs type/unify
- [ ] core/check 336 - needs type/unify
- [ ] core/inline 290 - needs simplify
- [ ] core/specialize 498 - needs simplify
- [ ] type/infermonad 1500 - needs type/unify
- [ ] type/infer 2300 - needs type/infermonad, core/analysismatch
- [ ] compile/* - needs lots + parallel / async features
- [ ] main 144 - needs everything
- [ ] main/language-server - needs everything + async + jsonrpc
- [ ] platform(as needed)

## Low priority
- [ ] interpreter/commands 318 - can be done
- [ ] syntax/colorize 607 - can be done
- [ ] backend/csharp/from-core 1884 - can be done
- [ ] backend/javascript/from-core 1371 - can be done
- [ ] syntax/gendoc 598 - needs colorize / highlight
- [ ] interpreter/interpret 734 - needs everything

# TODO: Language Server
Lots