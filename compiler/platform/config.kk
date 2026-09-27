// Ported as of 2026-01-17; approx upstream baseline commit edc29e7 of Platform/cpp/Platform/Config.hs (backfilled 2026-07-23)
module compiler/platform/config

import std/os/env

pub effect val comp-flags: compiler-flags;

pub fun @default-comp-flags(f)
  with handler val comp-flags = CompilerFlags(
    programName = "koka",
    version = "3.2.7",
    compiler = "koka",
    buildVariant = "release"
  )
  f()

pub type compiler-flags
  CompilerFlags(
    programName: string,
    version: string,
    compiler: string,
    buildVariant: string
  )

pub type file-config
  FileConfig(
    exeExt: string,
    dllExt: string,
    objExt: string,
    libExt: string,
    libPrefix: string
  )

pub fun os-config(): _ file-config
  match get-os-name()
    "linux" -> FileConfig(".so", ".o", ".a", "lib", "")
    "windows" -> FileConfig(".exe", ".dll", ".obj", ".lib", "")
    "macos" -> FileConfig(".dylib", ".o", ".a", "lib", "")

pub val source-ext = ".kk"

pub fun is-path-sep(c: char): bool
  c == '/' || c == '\\'