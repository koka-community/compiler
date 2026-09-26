import * as assert from 'assert'
import * as path from 'path'
import * as vscode from 'vscode'

// Times the edit loop an editor actually drives: open a module, then edit the
// unsaved buffer and wait for the server's diagnostics after each change. The
// module's imports stay in the server's session between edits, so this is the
// cost a user pays per edit.
//
// Opt-in, since it is slow and prints timings rather than asserting them:
//   KOKA_BENCH=1 [KOKA_BENCH_FILE=compiler/type/infer.kk] [KOKA_BENCH_EDITS=5] npm test
// Run it twice: the first run fills the server's build directory, the second
// opens the module against a warm one.

const EXTENSION_ID = 'koka.language-koka'
const ClientState = { Stopped: 1, Running: 2, Starting: 3 }
const sleep = (ms: number) => new Promise(r => setTimeout(r, ms))

type TestApi = {
  getLanguageClient: () => { state: number } | undefined
  getLanguageServer: () => { diagnosticsReceived: vscode.EventEmitter<vscode.Uri> } | undefined
}

suite('language server edit latency', function () {
  this.timeout(0)

  test('open, then edit the unsaved buffer', async function () {
    if (process.env.KOKA_BENCH !== '1') this.skip()
    const api = (await vscode.extensions.getExtension(EXTENSION_ID)!.activate()) as TestApi
    for (let i = 0; i < 120 && api.getLanguageClient()?.state !== ClientState.Running; i++) await sleep(500)
    assert.strictEqual(api.getLanguageClient()?.state, ClientState.Running, 'language client never reached Running')

    const file = path.resolve(process.env.KOKA_TEST_CWD!, process.env.KOKA_BENCH_FILE || 'compiler/type/infer.kk')
    const edits = Number(process.env.KOKA_BENCH_EDITS || 5)
    const server = api.getLanguageServer()!
    // Resolves on the next diagnostics for `file`; created BEFORE the action it
    // times. Rejects if the server stops or nothing arrives in time, so a dead
    // server fails the test instead of hanging it.
    const timeoutMs = Number(process.env.KOKA_BENCH_TIMEOUT_MS || 300_000)
    const nextDiagnostics = () => new Promise<void>((resolve, reject) => {
      const started = Date.now()
      const finish = (err?: Error) => { sub.dispose(); clearInterval(poll); err ? reject(err) : resolve() }
      const sub = server.diagnosticsReceived.event(uri => { if (uri.fsPath === file) finish() })
      const poll = setInterval(() => {
        if (api.getLanguageClient()?.state === ClientState.Stopped) finish(new Error('the language server stopped'))
        else if (Date.now() - started > timeoutMs) finish(new Error(`no diagnostics within ${timeoutMs} ms`))
      }, 250)
    })
    // the diagnostics themselves, not a count: a check that fails early is fast,
    // and its timing would pass for the edit loop's
    const report = (doc: vscode.TextDocument) => {
      const ds = vscode.languages.getDiagnostics(doc.uri)
      for (const d of ds) {
        console.log(`    ${vscode.DiagnosticSeverity[d.severity]} ${d.range.start.line + 1}: ${d.message.split('\n')[0]}`)
      }
      return ds
    }
    const errors = (ds: vscode.Diagnostic[]) => ds.filter(d => d.severity === vscode.DiagnosticSeverity.Error).length

    let arrived = nextDiagnostics()
    let t0 = Date.now()
    const doc = await vscode.workspace.openTextDocument(file)
    const editor = await vscode.window.showTextDocument(doc)
    await arrived
    console.log(`open   ${Date.now() - t0} ms  ${file}`)
    assert.strictEqual(errors(report(doc)), 0, 'the module does not check cleanly; its timings would be meaningless')

    for (let i = 1; i <= edits; i++) {
      arrived = nextDiagnostics()
      t0 = Date.now()
      const end = doc.lineAt(doc.lineCount - 1).range.end
      await editor.edit(eb => eb.insert(end, `\n// edit ${i}\n`))
      await arrived
      console.log(`edit ${i} ${Date.now() - t0} ms`)
      assert.strictEqual(errors(report(doc)), 0, `edit ${i} does not check cleanly`)
    }

    assert.notStrictEqual(api.getLanguageClient()?.state, ClientState.Stopped, 'the language server exited')
    // leave the file on disk untouched
    await vscode.commands.executeCommand('workbench.action.revertAndCloseActiveEditor')
  })
})
