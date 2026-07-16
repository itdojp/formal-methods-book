#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');
const { loadManifest, parseManifestCommand, validateManifest } = require('./example-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');

function usage(stream = process.stderr) {
  stream.write(
    'Usage: node scripts/run-example-manifest.js (--id ID | --lane pr-quick|nightly)\n',
  );
}

function parseArgs(argv) {
  let id = null;
  let lane = null;
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--id') {
      id = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--lane') {
      lane = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--help' || arg === '-h') {
      usage(process.stdout);
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  if ((id === null) === (lane === null)) {
    throw new Error('--id または --lane のいずれか一方を指定してください');
  }
  return { id, lane };
}

function writeText(filePath, value) {
  fs.writeFileSync(filePath, value, 'utf8');
}

function runEntry(entry, options = {}) {
  const repoRoot = path.resolve(options.repoRoot || REPO_ROOT);
  const emitOutput = options.emitOutput !== false;
  const artifactDir = path.join(repoRoot, '.artifacts', 'manifest', entry.id);
  fs.rmSync(artifactDir, { recursive: true, force: true });
  fs.mkdirSync(artifactDir, { recursive: true });

  const commandPath = path.join(artifactDir, 'command.txt');
  const stdoutPath = path.join(artifactDir, 'stdout.log');
  const stderrPath = path.join(artifactDir, 'stderr.log');
  const metadataPath = path.join(artifactDir, 'metadata.json');
  writeText(commandPath, `${entry.command}\n`);
  writeText(stdoutPath, '');
  writeText(stderrPath, '');

  const startedAt = new Date();
  const invocation = parseManifestCommand(entry);
  const result = spawnSync(invocation.executable, invocation.args, {
    cwd: repoRoot,
    encoding: 'utf8',
    maxBuffer: 128 * 1024 * 1024,
  });
  const finishedAt = new Date();
  const stdout = result.stdout || '';
  let stderr = result.stderr || '';
  if (result.error) stderr += `${stderr.endsWith('\n') || stderr.length === 0 ? '' : '\n'}${result.error.message}\n`;
  writeText(stdoutPath, stdout);
  writeText(stderrPath, stderr);

  const exitCode = Number.isInteger(result.status) ? result.status : 1;
  const exitCodeMatches = exitCode === entry.expected.exitCode;
  const stdoutMarkerFound = stdout.includes(entry.expected.stdoutMarker);
  const passed = exitCodeMatches && stdoutMarkerFound && !result.error;
  const metadata = {
    schemaVersion: 1,
    id: entry.id,
    tool: entry.tool,
    toolVersion: entry.version,
    chapter: entry.chapter,
    anchor: entry.anchor,
    lane: entry.lane,
    command: entry.command,
    expected: entry.expected,
    actual: {
      exitCode,
      stdoutMarkerFound,
    },
    result: passed ? 'passed' : 'failed',
    startedAt: startedAt.toISOString(),
    finishedAt: finishedAt.toISOString(),
    durationMs: finishedAt.getTime() - startedAt.getTime(),
  };
  writeText(metadataPath, `${JSON.stringify(metadata, null, 2)}\n`);

  if (emitOutput && stdout) process.stdout.write(stdout);
  if (emitOutput && stderr) process.stderr.write(stderr);
  if (emitOutput && !exitCodeMatches) {
    console.error(
      `::error title=Example ${entry.id}::expected exit ${entry.expected.exitCode}, got ${exitCode}`,
    );
  }
  if (emitOutput && !stdoutMarkerFound) {
    console.error(
      `::error title=Example ${entry.id}::stdout marker not found: ${entry.expected.stdoutMarker}`,
    );
  }
  if (emitOutput) console.log(`${passed ? 'PASS' : 'FAIL'}: ${entry.id} (${entry.tool} ${entry.version})`);
  return passed;
}

function main() {
  let selection;
  try {
    selection = parseArgs(process.argv.slice(2));
  } catch (error) {
    console.error(error.message);
    usage();
    process.exitCode = 2;
    return;
  }

  const { manifest, manifestPath } = loadManifest(REPO_ROOT);
  const errors = validateManifest(manifest, { rootDir: REPO_ROOT, manifestPath });
  if (errors.length > 0) {
    for (const error of errors) console.error(`::error file=${error.filePath},line=${error.line}::${error.message}`);
    console.error(`Manifest validation failed with ${errors.length} error(s).`);
    process.exitCode = 2;
    return;
  }

  let entries;
  if (selection.id !== null) {
    entries = manifest.examples.filter((entry) => entry.id === selection.id);
    if (entries.length === 0) {
      console.error(`Unknown example id: ${selection.id}`);
      process.exitCode = 2;
      return;
    }
  } else {
    entries = manifest.examples.filter((entry) => entry.lane === selection.lane);
    if (entries.length === 0) {
      console.error(`Unknown or empty lane: ${selection.lane}`);
      process.exitCode = 2;
      return;
    }
  }

  let passed = true;
  for (const entry of entries) {
    if (!runEntry(entry)) passed = false;
  }
  if (!passed) process.exitCode = 1;
}

if (require.main === module) main();

module.exports = { parseArgs, runEntry };
