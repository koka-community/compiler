# Porting TODOs

This file tracks inconsistencies and missing features identified while porting the Koka compiler from Haskell to Koka.

## `compiler/lib/printer.kk` (via `std/pretty/printer`)
- [ ] **File Buffering Performance**: The current `file-printer` reads the entire file into a string, appends to it, and writes it back on every flush. This is `O(N)` per write. 
    - **Fix**: Use append-mode file handles or proper buffered IO to achieve `O(1)` performance.

## `compiler/common/color-scheme.kk`
- [ ] **Relative Paths**: The `show-range` function currently has a `TODO` regarding printing paths relative to the current working directory (`cwd`).
    - **Fix**: Implement `relative-to-path` logic similar to Haskell's implementation.

## `compiler/common/range.kk`
- [ ] **Source Storage**: Koka stores source content as `string` (UTF-8), while Haskell uses `ByteString`. This might have performance or memory implications for large files.
    - **Action**: Evaluate if `string` is sufficient or if a raw byte buffer is needed.
- [ ] **Literate Script Support**: `extractLiterate` is missing.
    - **Fix**: Implement parsing/extraction for literate Koka files (`.lagda` style or similar if supported).
- [ ] **BOM Stripping**: `readInput` (or its equivalent) does not check for or strip the UTF-8 Byte Order Mark (BOM).
    - **Fix**: Add BOM detection to file reading.

## `compiler/common/failure.kk`
- [ ] **Stack Traces**: The `raise` function currently does not print stack traces in debug builds, marked by `// Figure out stack traces`.
    - **Fix**: Integrate with Koka's runtime stack trace capabilities if available.
- [ ] **Error Message Processing**: The `catch` handler has a `TODO` for adjusting error messages (e.g., stripping "user error:" or "IO Error:" prefixes).
    - **Fix**: Implement the string processing logic found in Haskell's `catchIO`.

## `compiler/kind/kind.kk`
- [ ] **Missing Helpers**: `kindAddArg` function is missing (also it seems to be unused in the Haskell codebase)

## `compiler/syntax/highlight.kk`
- [ ] **Isocline Integration**: `// TODO: Isocline stuff`
- [ ] **Formatting Attributes**: `// TODO: FmtAttr`

## `compiler/syntax/lexer.kk`
- **Note**: Literate script support (`extractLiterate`) is missing (tracked under `compiler/common/range.kk`).

## `compiler/syntax/parse.kk`
- [ ] **Handler Parsing**: `parse-handler-expr` has a `TODO` to fix parsing to match grammar precisely.
- [ ] **Raw Value Definitions**: `parse-handler-op` asks `// TODO: is "raw" needed for value definitions?`.

## `compiler/syntax/parse-type.kk`
- [ ] **Error Context**: `parse-type-binder` has a `TODO` to add error context.

## `compiler/syntax/builders.kk`
- [ ] **Record Operations**: `make-effect-decl` and `make-operation-decl` have `TODO` to use record operations.
- [ ] **Resume Parameters**: `bind-expr-to-val` has `TODO` to add parameters to resume.
