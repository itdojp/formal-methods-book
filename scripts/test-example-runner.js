#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const { parseArgs, runEntry, selectRelatedQuickEntries } = require('./run-example-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');

function assertEvidence(rootDir, id) {
  const artifactDir = path.join(rootDir, '.artifacts', 'manifest', id);
  for (const name of ['metadata.json', 'command.txt', 'stdout.log', 'stderr.log']) {
    assert(fs.statSync(path.join(artifactDir, name)).isFile(), `${id}: missing ${name}`);
  }
  return JSON.parse(fs.readFileSync(path.join(artifactDir, 'metadata.json'), 'utf8'));
}

function makeToolManifest(maxOutputBytes = 1024 * 1024) {
  return {
    schemaVersion: 1,
    policy: {
      artifact: { retentionDays: 1, maxOutputBytes, maxBytesPerExample: 1024 * 1024 },
      execution: {
        timeout: 'runner-enforced',
        stdoutStderr: 'runner-enforced',
        retainedToolOutput: 'post-run-retention-cap',
        memory: 'declared-budget-only',
      },
      updates: { procedure: [] },
    },
    tools: [{
      id: 'alloy',
      name: 'Alloy Analyzer',
      aliases: ['Alloy'],
      lane: 'pr-quick',
      reason: { ja: 'fixture', en: 'fixture' },
      version: '6.2.0',
      rustToolchain: 'nightly-fixture',
      rustToolchainManifest: {
        url: 'https://static.rust-lang.org/dist/fixture/channel-rust-nightly.toml',
        sha256: '1'.repeat(64),
      },
      embeddedCbmcVersion: '6.8.0',
      suiteVersion: 'fixture-suite',
      suiteCommit: '2'.repeat(40),
      yosysVersion: 'fixture-yosys',
      yosysCommit: '3'.repeat(40),
      bitwuzlaVersion: 'fixture-bitwuzla',
      bitwuzlaCommit: '4'.repeat(40),
      wrapper: 'tools/alloy-check.sh',
      distribution: { url: 'https://example.invalid/alloy.jar', sha256: '0'.repeat(64) },
      platforms: ['fixture'],
      sources: [],
    }],
  };
}

function main() {
  assert.throws(() => parseArgs([]), /specify exactly one/);
  assert.throws(() => parseArgs(['--id', 'example', '--lane', 'pr-quick']), /specify exactly one/);
  assert.throws(() => parseArgs(['--tool', 'alloy', '--changed-from', 'main']), /only valid with --lane pr-quick/);
  assert.deepStrictEqual(parseArgs(['--tool', 'alloy']), {
    id: null, lane: null, tool: 'alloy', changedFrom: null, changedTo: 'HEAD', profile: null,
  });

  const parent = path.join(REPO_ROOT, 'tools', '.tmp');
  fs.mkdirSync(parent, { recursive: true });
  const rootDir = fs.mkdtempSync(path.join(parent, 'example-runner-self-test-'));
  fs.mkdirSync(path.join(rootDir, 'tools'), { recursive: true });
  fs.mkdirSync(path.join(rootDir, 'examples'), { recursive: true });
  fs.writeFileSync(path.join(rootDir, 'examples', 'valid.als'), 'run {}\n');
  fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nprintf "expected marker\\n"\n');

  const base = {
    tool: 'alloy',
    chapter: 'chapter04',
    anchor: 'example-contracts',
    lane: 'pr-quick',
    references: [],
    assets: ['examples/valid.als'],
    config: null,
    command: 'bash tools/alloy-check.sh examples/valid.als',
    expected: { exitCode: 0, stdoutMarker: 'expected marker', outcome: 'success' },
    limits: {
      timeoutSeconds: 5,
      memoryMiB: 1024,
      seed: null,
      scope: 'fixture',
      depth: null,
      bound: 'fixture',
    },
  };

  try {
    const toolManifest = makeToolManifest();
    const success = { ...base, id: 'runner-success' };
    assert.strictEqual(runEntry(success, { repoRoot: rootDir, emitOutput: false, toolManifest }), true);
    const successMetadata = assertEvidence(rootDir, success.id);
    assert.strictEqual(successMetadata.toolVersion, '6.2.0');
    assert.deepStrictEqual(successMetadata.toolDependencies, {
      rustToolchain: 'nightly-fixture',
      embeddedCbmcVersion: '6.8.0',
      suiteVersion: 'fixture-suite',
      suiteCommit: '2'.repeat(40),
      yosysVersion: 'fixture-yosys',
      yosysCommit: '3'.repeat(40),
      bitwuzlaVersion: 'fixture-bitwuzla',
      bitwuzlaCommit: '4'.repeat(40),
      rustToolchainManifest: {
        url: 'https://static.rust-lang.org/dist/fixture/channel-rust-nightly.toml',
        sha256: '1'.repeat(64),
      },
      suiteDistribution: {
        url: 'https://example.invalid/alloy.jar',
        sha256: '0'.repeat(64),
      },
    });
    assert.strictEqual(successMetadata.actual.exitCode, 0);
    assert.strictEqual(successMetadata.actual.outcome, 'success');
    assert.strictEqual(successMetadata.limitEnforcement.memory, 'declared-budget-only');
    assert.strictEqual(successMetadata.result, 'passed');
    assert.match(successMetadata.input.hash, /^[0-9a-f]{64}$/);
    assert.strictEqual(successMetadata.input.files[0].path, 'examples/valid.als');

    fs.writeFileSync(
      path.join(rootDir, 'tools', 'alloy-check.sh'),
      '#!/usr/bin/env bash\nprintf "partial stdout\\n"\nprintf "diagnostic stderr\\n" >&2\nexit 7\n',
    );
    const failure = { ...base, id: 'runner-failure' };
    assert.strictEqual(runEntry(failure, { repoRoot: rootDir, emitOutput: false, toolManifest }), false);
    const failureMetadata = assertEvidence(rootDir, failure.id);
    assert.strictEqual(failureMetadata.actual.exitCode, 7);
    assert.strictEqual(failureMetadata.actual.outcome, 'tool-error');
    assert.strictEqual(failureMetadata.result, 'failed');

    fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nprintf "counterexample found\\n"\n');
    const counterexample = {
      ...base,
      id: 'runner-counterexample',
      expected: { exitCode: 0, stdoutMarker: 'counterexample found', outcome: 'counterexample' },
    };
    assert.strictEqual(runEntry(counterexample, { repoRoot: rootDir, emitOutput: false, toolManifest }), true);
    assert.strictEqual(assertEvidence(rootDir, counterexample.id).actual.outcome, 'counterexample');

    fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nprintf "solver returned unknown\\n"\n');
    const unknown = { ...base, id: 'runner-unknown' };
    assert.strictEqual(runEntry(unknown, { repoRoot: rootDir, emitOutput: false, toolManifest }), false);
    assert.strictEqual(assertEvidence(rootDir, unknown.id).actual.outcome, 'unknown');

    fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nsleep 2\n');
    const timedOut = { ...base, id: 'runner-timeout', limits: { ...base.limits, timeoutSeconds: 1 } };
    assert.strictEqual(runEntry(timedOut, { repoRoot: rootDir, emitOutput: false, toolManifest }), false);
    assert.strictEqual(assertEvidence(rootDir, timedOut.id).actual.outcome, 'timeout');

    fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nexit 124\n');
    const innerTimedOut = { ...base, id: 'runner-inner-timeout' };
    assert.strictEqual(runEntry(innerTimedOut, { repoRoot: rootDir, emitOutput: false, toolManifest }), false);
    assert.strictEqual(assertEvidence(rootDir, innerTimedOut.id).actual.outcome, 'timeout');

    fs.writeFileSync(path.join(rootDir, 'tools', 'alloy-check.sh'), '#!/usr/bin/env bash\nhead -c 2048 /dev/zero\n');
    const exhausted = { ...base, id: 'runner-resource' };
    const smallOutputManifest = makeToolManifest(128);
    assert.strictEqual(runEntry(exhausted, { repoRoot: rootDir, emitOutput: false, toolManifest: smallOutputManifest }), false);
    assert.strictEqual(assertEvidence(rootDir, exhausted.id).actual.outcome, 'resource-exhausted');

    const entries = [
      { ...base, id: 'one', references: ['src/ja/chapters/chapter04.md'] },
      { ...base, id: 'two', assets: ['examples/other.als'] },
    ];
    assert.deepStrictEqual(selectRelatedQuickEntries(entries, ['src/ja/chapters/chapter04.md']).entries.map((e) => e.id), ['one']);
    assert.deepStrictEqual(selectRelatedQuickEntries(entries, ['tools/tool-manifest.json']).entries.map((e) => e.id), ['one', 'two']);
  } finally {
    fs.rmSync(rootDir, { recursive: true, force: true });
  }

  console.log('OK: manifest runner covers evidence, hashes, outcomes, limits, and diff selection.');
}

main();
