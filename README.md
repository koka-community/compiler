# Self-Hosted Koka Compiler

Koka has a relatively simple compiler, and it should be mostly straightforward to implement it in itself.

First priorities are to get a formatter and package management? system working. 
For package management, I'm not thinking of anything huge to start out, mostly just grabbing repos from git (starting with koka-community packages), and storing them in some canonical place based on git hash.

The rationale behind the choice of these two features is that:

1. These particular features are things that are partially lacking in Koka's Haskell compiler
2. They provide a cornerstone for starting to replace Koka's Haskell compiler without having to support the full compiler pipeline (mostly just Syntax / Lexing / Parsing and Reading / Writing files)
3. They help us grow the ecosystem in ways that are semi-detached from the core efforts of the Koka project itself

Some major features missing to actually complete the full compiler transition are as follows:

- Standard Library Data Containers - Efficient Maps / Sets - for now we will just use what we have in `koka-community/std`
- Comprehensive async & threading support - we can probably make do with what we have, or start with a single threaded implementation

Given those two things, we could have a working compiler. 
However, Koka is much more than a compiler now - it is also a language server and interpreter which require the following:

- JSON-RPC support for the language server (Tim has a small sample using his fork of Koka with LibUV support)
- A few C libraries (isocline bindings)
- Language Server Library (ideally generated from the spec, with a couple of nice wrappers or utilities).

While implementing self-hosted Koka we should be concientious that the libraries and things we depend on can support usage in WASM.

For example we probably want to separate the interpreter and language server as external pieces, and not part of the core compiler libraries.

Additionally we should provide nice hooks into the compiler pipeline via effects:

This could for example allow:

- providing formatting options
- providing package resolvers
- providing different backends
- providing optimization passes
- adding a post-lexing macro pass

.. and in general a more extensible compiler.

While this is a goal that I see as worthy, I'm not sure if (Daan) the original author of Koka shares my views for such an extensible compiler.
However, I think we can agree that separating the core pieces of the code into a compiler library, and trying to acheive loose coupling between components is a good idea.
Thankfully the Koka compiler already is designed well which will help with acheiving low coupling.

# Notes on translation

There will of course be changes, as the Koka language has different features and strengths we can leverage than the original Koka Haskell compiler.

For example, all usages of type-classes will either be translated into:

- algebraic effects - for state / environment / reader / writer / logging / and error effects
- or implicits - for generic accessors, and other type-polymorphic code

Files that are translated will have a copyright that matches the Koka compiler's copyright acknowledging the original authors, as well as the translation author. 
The files will also have a comment with a hash indicating the commit of Koka's Haskell compiler that the source was last updated from, and comments explaining the differences, and the missing or incomplete features.

## Other Considerations

We have moved the pretty printer / json and console printer libraries to std, since they are generally useful. (They used to be in `compiler/lib`)

I don't know how much Koka wants to be a batteries included language, or a community library language, 
but we could separate out the pretty printer and the rest of the `compiler/lib` utilities into their own small packages potentially, or integrate more small things into `std`.