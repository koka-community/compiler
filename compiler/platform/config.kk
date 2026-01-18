import std/os/env

pub effect val comp-flags: compiler-flags;

fun @default-comp-flags(f)
  with handler val comp-flags = CompilerFlags(
    programName = "koka",
    version = "3.2.3",
    compiler = "koka",
    buildVariant = "release"
  )
  f()

type compiler-flags
  CompilerFlags(
    programName: string,
    version: string,
    compiler: string,
    buildVariant: string
  )

type file-config
  FileConfig(
    exeExt: string,
    dllExt: string,
    objExt: string,
    libExt: string,
    libPrefix: string
  )

fun os-config(): _ file-config
  match get-os-name()
    "linux" -> FileConfig(".so", ".o", ".a", "lib", "")
    "windows" -> FileConfig(".exe", ".dll", ".obj", ".lib", "")
    "macos" -> FileConfig(".dylib", ".o", ".a", "lib", "")

val source-ext = ".kk"

fun is-path-sep(c: char): bool
  c == '/' || c == '\\'