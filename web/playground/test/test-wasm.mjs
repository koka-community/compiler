#!/usr/bin/env node
/**
 * test-wasm.mjs
 *
 * Runs the WASM Koka compiler (koka-playground.wasm) the way the playground's
 * compiler worker does, compiles a program, then runs the generated JavaScript
 * with node and checks its output.
 *
 * Usage:
 *   node web/playground/test/test-wasm.mjs [file.kk expected-output-line]
 *
 * Expects (see scripts/playground.sh):
 *   - web/playground/public/koka-playground.wasm
 *   - lib/std/                (stdlib sources, mounted at /share/lib/std)
 *   - web/playground/public/precompiled/  (precompiled .kki/.mjs, mounted at /lib/js-debug)
 */

import fs from 'fs';
import os from 'os';
import path from 'path';
import { execFileSync } from 'child_process';
import { WASI, File, Directory, PreopenDirectory, OpenFile, ConsoleStdout } from '@bjorn3/browser_wasi_shim';

const ROOT = path.resolve(import.meta.dirname, '..', '..', '..');
const PUBLIC = path.join(ROOT, 'web', 'playground', 'public');

function loadDirToMap(fsDir, vfsPrefix, files) {
  if (!fs.existsSync(fsDir)) return;
  for (const entry of fs.readdirSync(fsDir, { withFileTypes: true })) {
    const fsPath = path.join(fsDir, entry.name);
    const vfsPath = vfsPrefix + '/' + entry.name;
    if (entry.isDirectory()) loadDirToMap(fsPath, vfsPath, files);
    else files.set(vfsPath, fs.readFileSync(fsPath, 'utf-8'));
  }
}

function buildDirectoryTree(files) {
  const root = new Map();
  const encoder = new TextEncoder();
  for (const [filePath, content] of files) {
    const parts = filePath.split('/').filter(Boolean);
    let current = root;
    for (let i = 0; i < parts.length - 1; i++) {
      if (!current.has(parts[i])) current.set(parts[i], new Directory(new Map()));
      current = current.get(parts[i]).contents;
    }
    current.set(parts[parts.length - 1], new File(encoder.encode(content)));
  }
  return new Directory(root);
}

function collectFiles(dir, prefix, out, decoder) {
  for (const [name, entry] of dir.contents) {
    const p = prefix ? prefix + '/' + name : name;
    if (entry instanceof File) out.set(p, decoder.decode(entry.data));
    else if (entry instanceof Directory) collectFiles(entry, p, out, decoder);
  }
}

async function main() {
  const [srcArg, expected] = process.argv.slice(2);
  const source = srcArg ? fs.readFileSync(srcArg, 'utf-8') : 'pub fun main()\n  println("hello " ++ (6*7).show)\n';
  const expect = srcArg ? expected : 'hello 42';
  // the module name the playground derives from the source (koka-lang.ts MODULE_NAME_RE)
  const header = source.match(/^\s*module\s+([a-zA-Z][a-zA-Z0-9_/-]*)/m);
  const moduleName = header ? header[1] : 'main';

  const wasmPath = path.join(PUBLIC, 'koka-playground.wasm');
  if (!fs.existsSync(wasmPath)) {
    console.error('ERROR: ' + wasmPath + ' not found. Run: scripts/playground.sh');
    process.exit(1);
  }
  const wasmModule = await WebAssembly.compile(fs.readFileSync(wasmPath));

  const files = new Map();
  loadDirToMap(path.join(ROOT, 'lib', 'std'), '/share/lib/std', files);
  loadDirToMap(path.join(PUBLIC, 'precompiled'), '/lib/js-debug', files);
  const rootDir = buildDirectoryTree(files);

  const stdout = [];
  const stderr = [];
  const wasi = new WASI(
    ['koka-playground', '--sharedir=/share', '--libdir=/lib', '--target=js', '--builddir=/.koka',
     '--include=/share/lib', '--include=/', '--console=raw', '-v1', moduleName],
    [],
    [
      new OpenFile(new File(new TextEncoder().encode(source))),
      ConsoleStdout.lineBuffered(line => stdout.push(line)),
      ConsoleStdout.lineBuffered(line => stderr.push(line)),
      new PreopenDirectory('/', rootDir.contents),
    ],
    { debug: false },
  );
  const instance = new WebAssembly.Instance(wasmModule, { wasi_snapshot_preview1: wasi.wasiImport });
  const t0 = Date.now();
  let exitCode = 0;
  try {
    exitCode = wasi.start(instance);
  } catch (e) {
    console.error('WASM exception:', e);
    exitCode = -1;
  }
  console.log(`compiler ran in ${Date.now() - t0}ms, exit code ${exitCode}`);

  const jsonLine = stdout.filter(l => l.startsWith('{')).pop() ?? '';
  let success = false;
  try { success = JSON.parse(jsonLine).success === true; } catch { /* */ }
  if (!success) {
    console.error('FAIL: compile result: ' + (jsonLine || '(none)'));
    stderr.slice(-20).forEach(l => console.error('  ' + l));
    process.exit(1);
  }

  // Write the build directory out and run the entry with node.
  const generated = new Map();
  const kokaDir = rootDir.contents.get('.koka');
  if (kokaDir instanceof Directory) collectFiles(kokaDir, '', generated, new TextDecoder());
  const out = fs.mkdtempSync(path.join(os.tmpdir(), 'koka-playground-'));
  for (const [p, content] of generated) {
    fs.mkdirSync(path.dirname(path.join(out, p)), { recursive: true });
    fs.writeFileSync(path.join(out, p), content);
  }
  // the `@main` wrapper, as the playground's module runner uses
  const entry = [...generated.keys()].find(p => p.endsWith('/' + moduleName + '__main.mjs'));
  if (!entry) {
    console.error('FAIL: no ' + moduleName + '__main.mjs among ' + generated.size + ' generated files');
    process.exit(1);
  }
  const output = execFileSync('node', [path.join(out, entry)], { encoding: 'utf-8' });
  fs.rmSync(out, { recursive: true, force: true });
  if (!output.split('\n').includes(expect)) {
    console.error('FAIL: expected output line ' + JSON.stringify(expect) + ', got:\n' + output);
    process.exit(1);
  }
  console.log('PASS: ' + JSON.stringify(expect));
}

main().catch(err => { console.error(err); process.exit(1); });
