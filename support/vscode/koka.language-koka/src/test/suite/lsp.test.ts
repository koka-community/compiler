import * as assert from 'assert'
import * as path from 'path'
import * as vscode from 'vscode'

const EXTENSION_ID = 'koka.language-koka'

type TestApi = {
  getLanguageClient: () => { state: number, sendRequest: Function } | undefined
}

// `State` from vscode-languageclient (lib/common/client.d.ts), inlined so the
// test does not depend on the runtime shape of that module. Note the order:
// Running is 2 and Starting is 3, NOT the other way round.
const ClientState = { Stopped: 1, Running: 2, Starting: 3 }

const sleep = (ms: number) => new Promise(r => setTimeout(r, ms))

async function activateExtension(): Promise<TestApi> {
  const ext = vscode.extensions.getExtension(EXTENSION_ID)
  assert.ok(ext, `extension ${EXTENSION_ID} not found`)
  const api = await ext!.activate()
  assert.ok(api, 'activate() returned no API -- cannot observe the language client')
  return api as TestApi
}

suite('koka language server', () => {
  suiteSetup(async () => {
    // Point the server at the compiler under test BEFORE it starts. The default
    // (`koka` on PATH) may be an unrelated install, which is exactly the
    // misconfiguration this suite is meant to catch.
    const cfg = vscode.workspace.getConfiguration('koka')
    await cfg.update('languageServer.compiler', process.env.KOKA_TEST_COMPILER,
                     vscode.ConfigurationTarget.Global)
    await cfg.update('languageServer.workingDirectory', process.env.KOKA_TEST_CWD,
                     vscode.ConfigurationTarget.Global)
    // No extra include/sharedir arguments: a compiler inside the repository must
    // find `lib` and `kklib` from its own location. If that regresses, the
    // standard-library test below fails.
    await cfg.update('languageServer.compilerArguments', [],
                     vscode.ConfigurationTarget.Global)
  })

  test('activates and reaches Running', async () => {
    const api = await activateExtension()
    for (let i = 0; i < 120 && api.getLanguageClient()?.state !== ClientState.Running; i++) {
      await sleep(500)
    }
    assert.strictEqual(api.getLanguageClient()?.state, ClientState.Running,
      'language client never reached Running')
  })

  test('checks a file that imports the standard library', async () => {
    const api = await activateExtension()
    const file = path.resolve(__dirname, '../fixtures/hello.kk')
    const doc = await vscode.workspace.openTextDocument(file)
    await vscode.window.showTextDocument(doc)

    // A first check compiles the standard library, so wait for the server to go
    // quiet rather than for a fixed time.
    let hover: vscode.Hover[] = []
    for (let i = 0; i < 240; i++) {
      await sleep(1000)
      if (api.getLanguageClient()?.state === ClientState.Stopped) break
      hover = await vscode.commands.executeCommand<vscode.Hover[]>(
        'vscode.executeHoverProvider', doc.uri, new vscode.Position(5, 9))
      if (hover && hover.length > 0) break
    }

    assert.notStrictEqual(api.getLanguageClient()?.state, ClientState.Stopped,
      'the language server DIED while checking the file ' +
      '(client state Stopped: the process exited, which the client reports as EPIPE)')
    assert.ok(hover && hover.length > 0,
      'no hover response for a std-library-importing file: the server is running ' +
      'but its analysis did not complete -- check that `lib` and `kklib` resolve')
  })

  test('stays alive after the check, and answers a second request', async () => {
    const api = await activateExtension()
    const file = path.resolve(__dirname, '../fixtures/hello.kk')
    const doc = await vscode.workspace.openTextDocument(file)

    // The reported failure appeared AFTER a completed load ("0 of 66 modules to
    // compile", then the connection erroring), so a single successful request is
    // not enough: hold and re-ask.
    await sleep(10_000)
    assert.notStrictEqual(api.getLanguageClient()?.state, ClientState.Stopped,
      'the language server exited after completing its work')
    const symbols = await vscode.commands.executeCommand(
      'vscode.executeDocumentSymbolProvider', doc.uri)
    assert.ok(symbols !== undefined,
      'document symbol request went unanswered after the first check')
  })
})
