// Port of the linking half of src/Compile/CodeGen.hs (`ccompile` +
// `codeGenLinkExe`), collapsed to a single invocation of the detected C
// toolchain (`fl.ccomp`, see compiler/compile/options.kk's `cc-from-path` --
// upstream `ccompile` similarly assembles its command line from a `CC`
// value's fields rather than hardcoding "clang").
//
// Every module's `.c` -- the entry's included -- is built into its own `.o`
// (in parallel, see `compile-objs`), and the final invocation LINKS those
// objects.
// It passes no source file, so `cc.ccFlagsCompile`'s `-c` is not used there.
//
// Every object -- kklib included -- comes from the build output directory,
// built by this compiler. There is no prebuilt object cache: objects from a
// different compiler can reference internal helper symbols this one does not
// emit, which surfaces only as an undefined-symbol link failure.
module compiler/compile/link
import std/os/path
import std/os/dir
import std/os/file
import std/os/process
import compiler/lib/log
import compiler/compile/options
import compiler/platform/config
import compiler/compile/cc
import std/os/env
import compiler/common/file
import compiler/common/syntax
import compiler/core/core
import compiler/core/parse
import compiler/common/parse

//---------------------------------------------------------------------------
// C libraries: upstream `copyCLibrary` / `searchCLibrary` / `vcpkgCLibrary` /
// `conanCLibrary` (Compile/CodeGen.hs).
//
// A module declares a native dependency with
// `extern import c { library="pcre2-8"; vcpkg="pcre2"; conan="pcre2/[>=10.37]" }`
// (e.g. std/text/regex.kk). The STATIC library file is searched
// for in the library directories (then installed via vcpkg, then conan),
// COPIED into the build output directory when newer, and linked from there by
// path. The `include` directory beside its `lib` directory goes on the
// compile of every module that declares or directly imports it.
//---------------------------------------------------------------------------

// upstream `systemLibDirs`, the default `ccompLibDirs`, in the same order.
// Kept out of the flags defaults: `ccompLibDirs` is part of the build-directory
// hash, and the search result is what matters.
pub fun target-lib-search-dirs(): ndet list<string>
  match get-os-name()
    "windows" -> []
    "macos" -> ["/usr/local/lib", "/usr/lib", "/lib", "/opt/homebrew/lib"]
    _ -> ["/usr/local/lib", "/usr/lib", "/lib", "/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu"]

// The `cc`'s library file for `clib` (also tried
// with a `lib` prefix when it has none), with upstream's debug suffixes for a
// debug build, in the first of `search-dirs` that has it. Returns the file and
// the include directory derived from where it was found
// (`<base>/lib/<file>` and `<base>/debug/lib/<file>` both give `<base>/include`).
pub fun search-c-library(fl: flags, clib: string, cc: cc, search-dirs: list<string>): io maybe<(string, list<string>)>
  val suffixes = match fl.build-type
    DebugFull -> ["d","_d","-d","-debug","_debug","-dbg","_dbg"]
    Debug -> ["d","_d","-d","-debug","_debug","-dbg","_dbg"]
    _ -> []
  val mainName = (cc.ccLibFile)(clib)
  val names = Cons(mainName, if mainName.starts-with("lib").is-just then [] else [(cc.ccLibFile)("lib" ++ clib)])
  fun variants(name: string): list<string>
    val ext = name.path.extname
    val stem = if ext == "" then name else name.list.take(name.count - ext.count - 1).string
    Cons(name, suffixes.map(fn(s) stem ++ s ++ (if ext == "" then "" else "." ++ ext)))
  val found = names.flatmap(variants).foldl(Nothing) fn(acc, file)
    match acc
      Just(_) -> acc
      Nothing -> search-dirs.find(fn(dir) (dir.path / file.path).is-file).map(fn(dir) (dir, file))
  match found
    Nothing -> Nothing
    Just((dir, file)) ->
      val dirp = dir.path
      val includes =
        if std/os/path/basename(dirp) == "lib" then
          val base = dirp.dirname.path
          if std/os/path/basename(base) == "debug" then [(base.dirname.path / "include".path).string]
          else [(base / "include".path).string]
        else []
      Just(((dirp / file.path).string, includes))

// Compiler-specific conan settings plus
// the shared build-type setting.
fun conan-settings-from-flags(fl: flags, cc: cc): ndet (list<string>, list<(string,string)>)
  val name = cc.ccName
  val runtimeSuffix = match fl.build-type
    DebugFull -> "MDd"
    Debug -> "MDd"
    _ -> "MD"
  val cl-runtime = ["-s", "compiler.runtime=" ++ runtimeSuffix]
  val settings =
    if name.starts-with("clang-cl").bool then cl-runtime
    elif name.starts-with("mingw").bool then []
    elif name.starts-with("emcc").bool then
      ["-s", "os=Emscripten"] ++
        (if fl.target.is-target-wasm then
           (if fl.targetPlatform.ptrSize == 4 then ["-s","arch=wasm"]
            elif fl.targetPlatform.ptrSize == 8 then ["-s","arch=wasm64"]
            else [])
         else [])
    elif name.starts-with("cl").bool then cl-runtime
    else []
  val buildTypeStr = match fl.build-type
    DebugFull -> "Debug"
    Debug -> "Debug"
    RelWithDebInfo -> "Release"
    Release -> "Release"
  val build = ["-s", "build_type=" ++ buildTypeStr]
  (build ++ settings,
   [("CC", cc.ccPath)] ++ (if cc/on-windows() then [("CONAN_CMAKE_GENERATOR", "Ninja")] else []))

// upstream `conanCLibrary`. `pkg` is e.g. "pcre2/[>=10.37]"; `pkgBase` is the
// part before the first "/" ("pcre2"), used for the shared/static-linkage
// option upstream passes to `conan install`.
fun conan-c-library(fl: flags, cc: cc, clib: string, pkg: string): io either<list<string>, (string, list<string>)>
  val isWindows = cc/on-windows()
  match search-path(fl.conan)
    Nothing ->
      Left(["this module requires a conan package but \"" ++ fl.conan ++ "\" is not installed.",
            "         install conan as:",
            "         > pip3 install conan",
            "         or see <https://docs.conan.io/en/latest/installation.html>"])
    Just(_conanCmd) | isWindows && !(["cl","clang-cl"].any(fn(p) cc.ccName.starts-with(p).bool)) ->
      Left(["conan can only be used with the 'cl' or 'clang-cl' compiler on Windows"])
    Just(_conanCmd) | fl.target.is-target-wasm ->
      Left(["conan can not be used with a wasm target"])
    Just(conanCmd) ->
      val pkgBase = match pkg.split("/") { Cons(b, _) -> b; Nil -> pkg }
      val (baseSettings, conanEnv) = conan-settings-from-flags(fl, cc)
      val settings = baseSettings ++ ["-o", pkgBase ++ "/*:shared=False", "-o", "shared=False"]
      fun run-conan-env(args: list<string>): io string
        // upstream `runCommandReadAll`/`runCommandEnv`: env vars set as
        // literal `KEY=VAL cmd ...` prefixes (portable across sh/bash, no
        // subprocess-env-map primitive needed here).
        val envPrefix = conanEnv.map(fn((k,v)) k ++ "=" ++ v.quoted).join(" ")
        val cmdline = (if envPrefix == "" then "" else envPrefix ++ " ") ++
                      (Cons(conanCmd, args).map(quoted)).join(" ") ++ " 2>&1"
        match run-system-read(cmdline)
          Ok(out) -> out
          Error(_) -> ""
      fun find-package-dir(): io maybe<(string,string)>
        val infoOut = run-conan-env([conanCmd, "list", "-c", pkg])
        // upstream: last non-blank line of `conan list -c pkg`'s output is
        // the resolved cache reference (e.g. "pcre2/10.42#abcd1234...").
        val infoLines = infoOut.lines.reverse.drop-while(fn(l) l.trim == "")
        val cachepkg = infoLines.head.default("").trim
        if !cachepkg.starts-with(pkgBase).bool then Nothing
        else
          val installOut = run-conan-env(Cons(conanCmd, ["install", "--requires", cachepkg]) ++ settings)
          val pathLinePrefix = cachepkg ++ ": Appending PATH environment variable: "
          val ppaths = installOut.lines.filter-map fn(line)
            match line.starts-with(pathLinePrefix)
              Just(restSlice) ->
                val rest = restSlice.string
                // upstream drops a trailing "/bin" (4 chars) off the appended path
                Just(if rest.count > 4 && rest.ends-with("/bin").bool
                     then rest.list.take(rest.count - 4).string else rest)
              Nothing -> Nothing
          match ppaths
            [ppath] -> if ppath.path.is-directory then Just((cachepkg, ppath)) else Nothing
            _ -> Nothing
      fun install-package(): io ()
        val installCmd = Cons(conanCmd, ["install", "--build", "missing", "--requires", pkg]) ++ settings
        if !fl.autoInstallLibs then
          println("warning: this module requires the conan package " ++ pkg ++
                    "\n         enable auto install using the \"--autoinstall\" option to koka," ++
                    "\n         or install the package manually as:" ++
                    "\n         > " ++ installCmd.join(" ") ++
                    "\n         to install the required C library and header files")
        else
          val _ = run-conan-env([conanCmd, "profile", "detect"])  // ensure a default profile exists
          println("install: conan package: " ++ pkg)
          val _ = run-conan-env(installCmd)
          ()
      match find-package-dir()
        Just((pkgName, pkgDir)) ->
          println("package : conan " ++ pkgName)
          match search-c-library(fl, clib, cc, [pkgDir ++ "/lib"])
            Just(res) -> Right(res)
            Nothing -> Left([])
        Nothing ->
          install-package()
          match find-package-dir()
            Just((pkgName, pkgDir)) ->
              println("package : conan " ++ pkgName)
              match search-c-library(fl, clib, cc, [pkgDir ++ "/lib"])
                Just(res) -> Right(res)
                Nothing -> Left([])
            Nothing -> Left(["unable to resolve conan package: " ++ pkg])

// `--vcpkg=<dir>`/`VCPKG_ROOT`, else search `PATH`
// (+ `~/vcpkg`, where `brew install vcpkg` places the binary) for the `vcpkg`
// executable.
fun vcpkg-find-root(vcpkg-root: string): io (string, string)
  val vcpkgExe = "vcpkg" ++ exe-extension()
  if vcpkg-root != "" then (vcpkg-root, vcpkg-root ++ "/" ++ vcpkgExe)
  else match get-env-value("VCPKG_ROOT")
    Just(eroot) | eroot != "" -> (eroot, eroot ++ "/" ++ vcpkgExe)
    _ ->
      val home = homedir().string
      match search-path("vcpkg", [home ++ "/vcpkg"])
        Nothing -> ("", vcpkgExe)
        Just(fname0) ->
          val fname = fname0.path.realpath.string
          val dir = fname.path.dirname
          // Homebrew-style keg layout: a "bin/vcpkg" symlink implies the
          // real root replaces "bin" with "libexec" in the same parent.
          val segs = dir.split("/")
          val root = match segs.reverse
            Cons("bin", rest) -> rest.reverse.join("/") ++ "/libexec"
            _ -> dir
          (root, fname)

// upstream `vcpkgCLibrary`.
fun vcpkg-c-library(fl: flags, cc: cc, clib: string, pkg: string): io either<list<string>, (string, list<string>)>
  val (root, vcpkgCmd) = vcpkg-find-root(fl.vcpkgRoot)
  if !vcpkgCmd.path.is-file then
    Left(["this module requires vcpkg to install the " ++ clib ++ " library.",
          "   hint: specify the root directory of vcpkg using the --vcpkg=<dir> option",
          "         or the VCPKG_ROOT environment variable," ++
          (if get-os-name() == "macos" then "\n         or install vcpkg as:\n         > brew install vcpkg"
           else "\n         or install vcpkg from <https://vcpkg.io/en/getting-started.html>")])
  else
    val debugish = match fl.build-type { DebugFull -> True; Debug -> True; _ -> False }
    val libDir = root ++ "/installed/" ++ fl.vcpkgTriplet ++ (if debugish then "/debug/lib" else "/lib")
    println("package : vcpkg " ++ pkg)
    match search-c-library(fl, clib, cc, [libDir])
      Just(res) -> Right(res)
      Nothing ->
        val packageDir = root ++ "/packages/" ++ pkg ++ "_" ++ fl.vcpkgTriplet
        if packageDir.path.is-directory then
          println("warning: vcpkg " ++ pkg ++ " is installed but the library " ++ clib ++
                    " is not found in " ++ libDir)
        val installCmd = [vcpkgCmd, "install", pkg ++ ":" ++ fl.vcpkgTriplet, "--disable-metrics"]
        if !fl.autoInstallLibs then
          println("warning: this module requires vcpkg package " ++ pkg ++
                    "\n   hint: enable auto install using the \"--autoinstall\" option to koka," ++
                    "\n         or install the package manually as:" ++
                    "\n         > " ++ installCmd.join(" ") ++
                    "\n         to install the required C library and header files")
          Left([])
        else
          println("install: vcpkg package: " ++ pkg)
          val _ = run-system-read(installCmd.map(quoted).join(" ") ++ " 2>&1")
          match search-c-library(fl, clib, cc, [libDir])
            Just(res) -> Right(res)
            Nothing -> Left([])

// upstream `externalImportsFromCore` / `clibsFromCore`: every `library`
// declaration of a core (resolved for the build type), with its own
// `vcpkg`/`conan` package hints.
pub fun clibs-of-core(c: core, bt: buildType): _ list<(string, maybe<string>, maybe<string>)>
  c.externals.filter-map fn(e)
    match external-import-lookup(bt, "library", e)
      Nothing -> Nothing
      Just(lib) -> Just((lib, external-import-lookup(bt, "vcpkg", e), external-import-lookup(bt, "conan", e)))

// The `syslib` declarations, split on `;`
pub fun csyslibs-of-core(c: core, bt: buildType): _ list<string>
  c.externals.filter-map(fn(e) external-import-lookup(bt, "syslib", e)).flatmap(fn(s) s.split(";"))

// A C translation unit plus the `extern import` library declarations it is
// compiled against: its own module's and its direct imports' (upstream
// `codeGen`: `eimports` over `bcore : importcores`).
pub struct c-unit
  cfile: path
  eimports: list<(string, maybe<string>, maybe<string>)> = []

fun nub-strings(xs: list<string>): list<string>
  xs.foldl([]) fn(acc, x) if acc.any(fn(y) y == x) then acc else acc ++ [x]

fun decl-eq(a: (string, maybe<string>, maybe<string>), b: (string, maybe<string>, maybe<string>)): bool
  val (l1, v1, c1) = a
  val (l2, v2, c2) = b
  l1 == l2 && v1.default("") == v2.default("") && v1.is-just == v2.is-just &&
    c1.default("") == c2.default("") && c1.is-just == c2.is-just

pub fun nub-decls(xs: list<(string, maybe<string>, maybe<string>)>): list<(string, maybe<string>, maybe<string>)>
  xs.foldl([]) fn(acc, x) if acc.any(fn(y) decl-eq(x, y)) then acc else acc ++ [x]

// Find the static library and copy it into the
// output directory when newer (so it can be linked, and bundled, from there),
// returning the include directories its users compile against.
pub fun copy-c-library(fl: flags, c: cc, out-dir: path, decl: (string, maybe<string>, maybe<string>)): <io,log> list<string>
  val (clib, vcpkgPkg, conanPkg) = decl
  val found = match search-c-library(fl, clib, c, fl.ccompLibDirs ++ target-lib-search-dirs())
    Just(res) -> Just(res)
    Nothing ->
      val viaVcpkg = match vcpkgPkg
        Just(pkg) -> vcpkg-c-library(fl, c, clib, pkg)
        Nothing -> Left([])
      match viaVcpkg
        Right(res) -> Just(res)
        Left(vcpkgWarns) ->
          val viaConan = match conanPkg
            Just(pkg) -> conan-c-library(fl, c, clib, pkg)
            Nothing -> Left([])
          match viaConan
            Right(res) -> Just(res)
            Left(conanWarns) ->
              (vcpkgWarns ++ conanWarns).foreach(fn(w) println("warning: " ++ w))
              Nothing
  match found
    Just((libPath, includes)) ->
      val outLib = out-dir / (c.ccLibFile)(clib).path
      // upstream only reports and copies when the file actually changed
      if libPath != outLib.string && file-mtime(libPath.path) > file-mtime(outLib) then
        phase("library", libPath)
        copy-file(libPath.path, outLib)
      includes
    Nothing ->
      println("warning: unable to find C library: " ++ clib ++
              "\n   hint: provide \"--cclibdir\" as an option, or use \"syslib\" in an extern import?")
      []

// The include directories of each unit, copying each distinct library once.
// Not de-duplicated per unit: upstream's `extraIncDirs` is the plain
// concatenation over the unit's declarations.
fun units-include-dirs(fl: flags, c: cc, out-dir: path, units: list<c-unit>): <io,log> list<list<string>>
  val decls = nub-decls(units.flatmap(fn(u) u.eimports))
  val table = decls.map(fn(d) (d, copy-c-library(fl, c, out-dir, d)))
  units.map fn(u)
    nub-decls(u.eimports).flatmap fn(d)
      match table.find(fn((d2, _)) decl-eq(d, d2))
        Just((_, incs)) -> incs
        Nothing -> []

// Compile `sources` to `target-obj`.
fun ccompile-args(fl: flags, c: cc, target-obj: path, extra-inc-dirs: list<string>, sources: list<path>,
                  kklibInclude: path, extra-defs: list<(string,string)> = []): ndet list<string>
  [c.ccPath] ++
  c.ccFlags ++
  c.ccFlagsWarn ++
  cc/flags-build(c, fl.build-type, fl.optimize, fl.targetArch) ++
  c.ccFlagsCompile ++
  (c.ccIncludeDir)(kklibInclude.string.quoted) ++
  (extra-inc-dirs ++ fl.ccompIncludeDirs).flatmap(fn(d) (c.ccIncludeDir)(d.quoted)) ++
  (fl.ccompDefs ++ extra-defs).flatmap(fn(d) (c.ccAddDef)(d)) ++
  (c.ccTargetObj)(target-obj.string).map(fn(t) if t.starts-with("-").is-just then t else t.quoted) ++
  sources.map(fn(s) s.string.quoted)

// upstream `codeGenLinkC` + `codeGenLinkExe`: compile any stale units, then
// link kklib, the imported modules in BUILD ORDER and the entry -- objects
// only, and the libraries by their copied paths. Returns `Nothing` on success,
// `Just(output)` with the captured diagnostics on failure.
//
// A SOURCE file on the link line would make clang compile and link in one
// invocation, and with `-g` it then runs `dsymutil` over the whole executable
// on macOS (20.6s, serial, on every warm build of the compiler).
pub fun c-link(fl: flags, entry: c-unit, outExe: path, kklibInclude: path,
               // imported modules compiled from source, in build order
               imports: list<c-unit> = [],
               // every `library` declaration of the closure
               clibs: list<(string, maybe<string>, maybe<string>)> = [],
               // every `syslib` of the imported modules
               csyslibs: list<string> = []): _ maybe<string>
  val c = fl.ccomp
  val out-dir = entry.cfile.dirname.path
  val kklibObj = match kklib-build(fl, c, out-dir, kklibInclude)
    Left(err) -> return Just("compiler/compile/link: cannot build kklib:\n" ++ err)
    Right(o) -> o
  val units = imports ++ [entry]
  val objs = compile-objs(fl, c, units, out-dir, kklibInclude)
  // The batch discards each job's own output (see `compile-objs`), so a `.o`
  // that did not appear is re-run singly, with its output captured, to get a
  // real diagnostic instead of a cryptic "no such file" from the link.
  val retryFailures = units.zip(objs).filter(fn((_, o)) !o.is-file).filter-map fn((u, o))
    match c-compile-module(fl, u, kklibInclude)
      Just(err) -> Just(o.string ++ ":\n" ++ err)
      Nothing -> if o.is-file then Nothing
                 else Just(o.string ++ ": (missing after retry, no diagnostic captured)")
  if !retryFailures.is-nil then Just(retryFailures.join("\n"))
  else
    // each library was copied when a unit using it was compiled; make sure of
    // it here too (a stat when already in place)
    val libs = nub-strings(nub-decls(clibs).flatmap(fn(d) { val _ = copy-c-library(fl, c, out-dir, d); val (l, _, _) = d; l.split(";") }))
    val libpaths = libs.map(fn(l) (out-dir / (c.ccLibFile)(l).path).string)
    val syslibs = nub-strings(csyslibs ++ fl.ccompLinkSysLibs ++ ["m", "pthread"])
    // wasm stacks default to 64KB, too small for Koka's recursion. emscripten
    // also fixes its memory at 16MB unless told otherwise, too small for
    // mimalloc, which faults on its first allocation; wasi-sdk's memory grows.
    val stksize = if fl.stackSize == 0 && (on-windows() || fl.target.is-target-wasm) then 8*1024*1024 else fl.stackSize
    val hpsize = if fl.heapSize == 0 && fl.target.is-target-wasm && c.ccName.starts-with("emcc").bool then 1024*1024*1024 else fl.heapSize
    val cmd =
      [c.ccPath] ++
      c.ccFlags ++
      cc/flags-build(c, fl.build-type, fl.optimize, fl.targetArch) ++
      (c.ccTargetExe)(outExe.string).map(fn(t) if t.starts-with("-").is-just then t else t.quoted) ++
      Cons(kklibObj, objs).map(fn(o) o.string.quoted) ++
      c.ccFlagsLink ++
      (c.ccFlagStack)(stksize) ++
      (c.ccFlagHeap)(hpsize) ++
      libpaths.flatmap(fn(l) (c.ccAddLib)(l.quoted)) ++
      syslibs.flatmap(fn(l) (c.ccAddSysLib)(l))
    run-cc(cmd.join(" "), outExe)

// Compile `<kklibdir>/src/all.c` into
// `<outDir>/kklib.o` for the current build variant, skipping the work when the
// object is newer than `include/kklib.h`. Upstream keeps this object in the
// build output directory alongside every module's own `.o`; so does this port.
pub fun kklib-build(fl: flags, c: cc, out-dir: path, kklib-include: path): _ either<string, path>
  val objPath = out-dir / ((c.ccObjFile)("kklib")).path
  val srcDir = kklib-include.dirname.path          // <kklib>/include -> <kklib>
  val allC = srcDir / "src".path / "all.c".path
  if !allC.is-file then
    Left("cannot find kklib sources at " ++ allC.string ++
         "\n   hint: check --kklibdir; kklib lives in this repository, under kklib/")
  elif objPath.is-file && !fl.rebuild &&
       file-mtime(kklib-include / "kklib.h".path) <= file-mtime(objPath) then
    Right(objPath)
  else
    phase("compile", "kklib from: " ++ srcDir.string)
    // upstream: mimalloc's include dir appended to `ccompIncludeDirs` unless
    // --fstdalloc, and the version/compiler-name defines appended to
    // `ccompDefs`. The command runs through a shell, so the quotes of those
    // two string-valued defines must survive it; upstream execs clang directly.
    val incs = if fl.useStdAlloc then [] else [(srcDir / "mimalloc".path / "include".path).string]
    val defs = [("KK_COMP_VERSION", "\\\"" ++ comp-flags.version ++ "\\\""),
                ("KK_CC_NAME", "\\\"" ++ c.ccName ++ "\\\"")]
    val cmd = ccompile-args(fl(ccompIncludeDirs = fl.ccompIncludeDirs ++ incs), c, objPath, [], [allC], kklib-include, defs).join(" ")
    phase-verbose(3, "command", cmd)
    val (out, exitcode) = run-cc-raw(cmd ++ " 2>&1")
    if exitcode == 0 then Right(objPath) else Left(out)

// Compile ONE unit's .c to its sibling .o, with its output captured (used to
// get a diagnostic for a unit the batch failed on). Skips when the .o is
// newer than the .c.
pub fun c-compile-module(fl: flags, unit: c-unit, kklibInclude: path): <io,log> maybe<string>
  val obj = unit.cfile.change-ext("o")
  val ot = file-mtime(obj)
  if ot > 0 && file-mtime(unit.cfile) <= ot then Nothing
  else
    val c = fl.ccomp
    val incs = units-include-dirs(fl, c, unit.cfile.dirname.path, [unit]).head.default([])
    val cmd = ccompile-args(fl, c, obj, incs, [unit.cfile], kklibInclude).join(" ")
    phase-verbose(3, "command", cmd)
    val (out, exitcode) = run-cc-raw(cmd ++ " 2>&1")
    if exitcode == 0 then Nothing else Just(out)

// Compile the closure's generated C to sibling .o files.
//
// Upstream (`CodeGen.hs:318`) runs `ccompile` for EVERY module and gates only
// the LINK on having an entry. A LIBRARY build never reaches `c-link`, so the
// build calls this for it; after an entry build it is a stat loop.
pub fun c-compile-objects(fl: flags, units: list<c-unit>, kklibInclude: path): <io,log> ()
  match units
    Nil -> ()
    Cons(u, _) ->
      val _ = compile-objs(fl, fl.ccomp, units, u.cfile.dirname.path, kklibInclude)
      ()

// Compile each unit's .c to a sibling .o, `cc-jobs()` at a time, skipping any
// whose .o is newer than its source. Returns the .o paths in the given order.
//
// Every job runs upstream's own per-file `ccompile` command line (echoed at
// verbose 3, exactly what runs). They go through ONE `xargs -P` rather than a
// process per spawn from here, and each job discards its own stdout+stderr
// instead of writing to the shared pipe `run-cc-raw` captures: funneling every
// concurrent clang's output through one pipe measured wall 10.4s -> 28.0s and
// sys 3.5s -> 135.9s from kernel-side pipe contention alone. Only a failure's
// output matters, and `c-link` re-runs a missing `.o` singly to capture it.
fun compile-objs(fl: flags, c: cc, units: list<c-unit>, out-dir: path, kklibInclude: path): <io,log> list<path>
  val objs = units.map(fn(u) u.cfile.change-ext("o"))
  // Only rebuild what is stale: this is the whole point of per-module objects.
  //
  // Comparing against the `.c` alone is sound only because a recompiled module
  // always REWRITES its `.c`. An object also depends on its imports' headers,
  // which are not tracked here, so writing a `.c` only when its content differs
  // would keep objects compiled against headers that have since changed; such
  // a scheme has to track header generations as well.
  val stale = units.zip(objs).filter fn((u, ob))
    val ot = file-mtime(ob)
    ot <= 0 || file-mtime(u.cfile) > ot
  // the same unit can appear twice (a module aliased under two names)
  val stale1 = stale.foldl([]) fn(acc, uo)
    val (u, _) = uo
    if acc.any(fn((u2, _)) u2.cfile.string == u.cfile.string) then acc else acc ++ [uo]
  if get-env-value("KOKA_CC_DEBUG").is-just then
    println("CC-STALE: " ++ stale1.length.show ++ " of " ++ units.length.show)
  if stale1.is-nil then objs
  else
    val incs = units-include-dirs(fl, c, out-dir, stale1.map(fst))
    // Each job first removes the object it replaces: the batch discards every
    // job's status, so a compile that fails without touching its output (a
    // compiler that does not start) would otherwise leave the previous object
    // in place, and the link would silently use it.
    val cmds = stale1.zip(incs).map fn((uo, inc))
      val (u, ob) = uo
      "rm -f " ++ ob.string.quoted ++ "; " ++ ccompile-args(fl, c, ob, inc, [u.cfile], kklibInclude).join(" ")
    cmds.foreach(fn(cmd) phase-verbose(3, "command", cmd))
    val jobs = out-dir / ".cc-jobs".path
    write-text-file(jobs, cmds.join("\n") ++ "\n")
    val cmdline = "tr '\\n' '\\000' < " ++ jobs.string.quoted ++ " | xargs -0 -P " ++ cc-jobs().show ++
                  " -n 1 sh -c 'eval \"$1\" > /dev/null 2>&1' _"
    if get-env-value("KOKA_CC_DEBUG").is-just then println("CC-CMD: " ++ cmdline)
    val _ = run-cc-raw(cmdline)
    objs

// How many C compiles to run at once. Kept modest: each clang on generated
// Koka C is memory-hungry (the largest TU here is 18.6MB of source).
// C translation units have no dependencies on each other, so the batch
// compile is embarrassingly parallel -- there is no reason to under-provision
// it. Measured standalone on 67 generated TUs (build.kk's closure): `-P 8`
// gave 26.4s wall (2.43x); `-P 14` (this machine's full core count) gave
// 10.4s wall (6.1x). A hardcoded default of 8 was leaving more than half the
// available speedup on the table for no benefit -- these are independent
// clang PROCESSES with their own address spaces, not threads sharing memory,
// so the memory-pressure concern that motivates capping `compute` concurrency
// does not apply the same way here.
fun cc-jobs(): io int
  match get-env-value("KOKA_CC_JOBS")
    Just(s) -> s.parse-int.default(get-cpu-count())
    Nothing -> get-cpu-count()


// upstream `runCommand`: echoed at verbose 3 as `command`, and failed by a
// non-zero exit status. A produced file is no success signal: one from an
// earlier build survives a compiler that fails without writing it.
fun run-cc(cmdline: string, outExe: path): <io,log> maybe<string>
  phase-verbose(3, "command", cmdline)
  val (out, exitcode) = run-cc-raw(cmdline ++ " 2>&1")
  if exitcode == 0 then Nothing else Just(out)

// Run `cmdline` through the shell; its stdout and exit status. `run-system-read`
// is a plain `popen` (kklib `kk_os_run_command`) that hides the child's status,
// so the status is echoed after the output behind a marker and parsed back off.
fun run-cc-raw(cmdline: string): io (string, int)
  val marker = "__KOKA_EXIT__"
  match run-system-read("{ " ++ cmdline ++ "\n}; echo " ++ marker ++ "$?")
    Ok(all) ->
      match all.split(marker).reverse
        Cons(status, Cons(last, before)) -> (Cons(last, before).reverse.join(marker), status.trim.parse-int.default(-1))
        _ -> (all, -1)
    Error(exn) -> (exn.message, -1)

fun quoted(s: string): string
  "\"" ++ s ++ "\""

// upstream `codeGenLinkExe`'s final step for a non-wasm C target: just run
// the produced executable and return its stdout+exit code.
pub fun run-exe(exePath: path, args: list<string> = []): io (string, int)
  val argsStr = if args.is-nil then "" else " " ++ args.join(" ")
  // do NOT merge the child's stderr: upstream `runSystemEcho` lets the
  // program's stderr flow to the terminal's stderr, which Spec.hs never
  // captures (e.g. `trace()` output is excluded from expected test output)
  run-cc-raw(exePath.string.quoted ++ argsStr)

// analog of `run-exe` for the JS target: run `jsFile` under `nodeCmd`
// (upstream `codeGenLinkExe`'s non-C branch invokes `node <mjs>`).
pub fun run-js(nodeCmd: string, jsFile: path, args: list<string> = []): io (string, int)
  val argsStr = if args.is-nil then "" else " " ++ args.join(" ")
  // same stderr policy as run-exe above
  run-cc-raw(nodeCmd.quoted ++ " " ++ jsFile.string.quoted ++ argsStr)
