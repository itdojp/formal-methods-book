#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const { parseArgs, runEntry } = require('./run-example-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');

function assertEvidence(rootDir, id) {
  const artifactDir = path.join(rootDir, '.artifacts', 'manifest', id);
  for (const name of ['metadata.json', 'command.txt', 'stdout.log', 'stderr.log']) {
    assert(fs.statSync(path.join(artifactDir, name)).isFile(), `${id}: missing ${name}`);
  }
  return JSON.parse(fs.readFileSync(path.join(artifactDir, 'metadata.json'), 'utf8'));
}

function main() {
  assert.throws(() => parseArgs([]), /specify exactly one of --id or --lane/);
  assert.throws(
    () => parseArgs(['--id', 'example', '--lane', 'pr-quick']),
    /specify exactly one of --id or --lane/,
  );

  const parent = path.join(REPO_ROOT, 'tools', '.tmp');
  fs.mkdirSync(parent, { recursive: true });
  const rootDir = fs.mkdtempSync(path.join(parent, 'example-runner-self-test-'));
  fs.mkdirSync(path.join(rootDir, 'tools'), { recursive: true });
  fs.mkdirSync(path.join(rootDir, 'examples'), { recursive: true });
  fs.writeFileSync(path.join(rootDir, 'examples', 'valid.als'), 'run {}\n');
  fs.writeFileSync(
    path.join(rootDir, 'tools', 'alloy-check.sh'),
    '#!/usr/bin/env bash\nprintf "expected marker\\n"\n',
  );

  const base = {
    tool: 'alloy',
    version: '6.2.0',
    chapter: 'chapter04',
    anchor: 'example-contracts',
    lane: 'pr-quick',
    assets: ['examples/valid.als'],
    config: null,
    command: 'bash tools/alloy-check.sh examples/valid.als',
    expected: { exitCode: 0, stdoutMarker: 'expected marker' },
  };

  try {
    const success = { ...base, id: 'runner-success' };
    assert.strictEqual(runEntry(success, { repoRoot: rootDir, emitOutput: false }), true);
    const successMetadata = assertEvidence(rootDir, success.id);
    assert.strictEqual(successMetadata.toolVersion, '6.2.0');
    assert.strictEqual(successMetadata.actual.exitCode, 0);
    assert.strictEqual(successMetadata.result, 'passed');

    fs.writeFileSync(
      path.join(rootDir, 'tools', 'alloy-check.sh'),
      '#!/usr/bin/env bash\nprintf "partial stdout\\n"\nprintf "diagnostic stderr\\n" >&2\nexit 7\n',
    );
    const failure = { ...base, id: 'runner-failure' };
    assert.strictEqual(runEntry(failure, { repoRoot: rootDir, emitOutput: false }), false);
    const failureMetadata = assertEvidence(rootDir, failure.id);
    assert.strictEqual(failureMetadata.toolVersion, '6.2.0');
    assert.strictEqual(failureMetadata.actual.exitCode, 7);
    assert.strictEqual(failureMetadata.actual.stdoutMarkerFound, false);
    assert.strictEqual(failureMetadata.result, 'failed');
    assert.match(
      fs.readFileSync(path.join(rootDir, '.artifacts', 'manifest', failure.id, 'stderr.log'), 'utf8'),
      /diagnostic stderr/,
    );
  } finally {
    fs.rmSync(rootDir, { recursive: true, force: true });
  }

  console.log('OK: manifest runner writes complete evidence for success and failure.');
}

main();
