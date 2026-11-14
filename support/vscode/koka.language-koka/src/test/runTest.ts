import * as path from 'path'
import * as fs from 'fs'
import * as os from 'os'
import { runTests, downloadAndUnzipVSCode } from '@vscode/test-electron'

// Launches a real VS Code with this extension loaded and runs the suite in it.
//
// KOKA_TEST_COMPILER  path to the compiler the language server should use.
//                     Defaults to the repository's pinned driver, which is what
//                     a developer actually runs.
// KOKA_TEST_CWD       the language server's working directory (repo root).
async function main() {
  const extensionDevelopmentPath = path.resolve(__dirname, '../../')
  const extensionTestsPath = path.resolve(__dirname, './suite/index')

  const repoRoot = path.resolve(extensionDevelopmentPath, '../../../')
  const defaultCompiler = path.join(repoRoot, '.koka', 'bootstrap', 'driver')
  const compiler = process.env.KOKA_TEST_COMPILER || defaultCompiler
  if (!fs.existsSync(compiler)) {
    console.error(`no compiler at ${compiler}\n` +
      `build one (scripts/build-driver.sh) or set KOKA_TEST_COMPILER`)
    process.exit(1)
  }
  console.log(`integration test: compiler=${compiler}`)
  const cwd = process.env.KOKA_TEST_CWD || repoRoot

  // A fresh workspace of two folders whose settings select the compiler under test.
  // Each folder is opened through a symbolic link (a junction on Windows), so the
  // paths in the editor differ from the real paths the compiler uses
  // (koka-lang/koka#970, #810).
  function linkedFolder(name: string): string {
    const real = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), `koka-vscode-${name}-`))
    fs.symlinkSync(real, real + '-link', 'junction')
    return real + '-link'
  }
  const folders = [linkedFolder('test'), linkedFolder('lib')]
  const workspace = path.join(path.dirname(folders[0]), path.basename(folders[0]) + '.code-workspace')
  fs.writeFileSync(workspace, JSON.stringify({
    folders: folders.map(folder => ({ path: folder })),
    settings: {
      'koka.languageServer.compiler': compiler,
      'koka.languageServer.workingDirectory': cwd,
      'koka.languageServer.compilerArguments': [],
    },
  }, null, 2))

  const shortBase = '/tmp/koka-vsc-test'
  const userDataDir = path.join(shortBase, 'ud')
  const extensionsDir = path.join(shortBase, 'ext')
  fs.mkdirSync(userDataDir, { recursive: true })
  fs.mkdirSync(extensionsDir, { recursive: true })

  // Resolve the executable ourselves: the macOS bundle's binary is
  // `Contents/MacOS/Code`, and a test-electron release that expects `Electron`
  // fails with ENOENT after a 300MB download.
  let vscodeExecutablePath = await downloadAndUnzipVSCode()
  if (!fs.existsSync(vscodeExecutablePath)) {
    const alt = vscodeExecutablePath.replace(/\/Electron$/, '/Code')
    if (fs.existsSync(alt)) vscodeExecutablePath = alt
    else throw new Error(`no VS Code executable at ${vscodeExecutablePath} (nor ${alt})`)
  }
  console.log(`integration test: vscode=${vscodeExecutablePath}`)

  await runTests({
    vscodeExecutablePath,
    extensionDevelopmentPath,
    extensionTestsPath,
    launchArgs: [
      workspace,
      // other extensions must not race this one for the .kk language id
      '--disable-extensions',
      '--disable-gpu',
      // SHORT paths on purpose: VS Code opens a unix socket under the user-data
      // dir, and macOS rejects socket paths beyond ~104 characters -- the
      // default (.vscode-test inside this repository) is well past that and
      // fails with `listen EINVAL`.
      `--user-data-dir=${userDataDir}`,
      `--extensions-dir=${extensionsDir}`,
    ],
    extensionTestsEnv: {
      KOKA_TEST_COMPILER: compiler,
      KOKA_TEST_CWD: cwd,
    },
  })
}

main().catch(err => { console.error('integration test failed:', err); process.exit(1) })
