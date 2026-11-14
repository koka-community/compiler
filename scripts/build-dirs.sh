# Sourced (with ROOT set to the repository) by the build, gate and benchmark
# scripts. A build directory is named .koka/v<version>[-<buildtag>] after the
# version of the compiler that WRITES it: the reference compiler's for a
# `./koka` build, the port's (compiler/platform/config.kk) for anything a port
# binary builds. The two versions move independently, so neither is spelled out
# in a script -- a stale one made the std-warm cleanup delete nothing and the
# gate find no binary.
KOKA_DEV_DIR="${KOKA_DEV_DIR:-$HOME/koka/.worktrees/dev-compiler}"
REF_KOKA=$(cd "$KOKA_DEV_DIR" && stack exec which koka)
REF_VERSION=$("$REF_KOKA" --version | sed -n 's/^version: *//p')
PORT_VERSION=$(sed -n 's/^ *version = "\([^"]*\)",$/\1/p' "$ROOT/compiler/platform/config.kk")
if [ -z "$REF_VERSION" ] || [ -z "$PORT_VERSION" ]; then
  echo "[build-dirs] cannot determine compiler versions (reference '$REF_VERSION', port '$PORT_VERSION')" >&2
  exit 1
fi
# the reference compiler's untagged output, where `./koka -c compiler/main/driver.kk` puts the driver
REF_DIR=$ROOT/.koka/v$REF_VERSION
# port_dir <buildtag>: where a port binary run with --buildtag=<buildtag> writes
port_dir() { echo "$ROOT/.koka/v$PORT_VERSION-$1"; }
