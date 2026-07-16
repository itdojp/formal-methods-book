#!/usr/bin/env node
'use strict';

const assert = require('assert');
const path = require('path');
const {
  createBuildProvenance,
  readJson,
  serializeBuildProvenance,
  validateBuildProvenance,
} = require('./lib/build-provenance');

const repoRoot = path.resolve(__dirname, '..');
const manifest = readJson(path.join(repoRoot, 'book-config.json'));
const input = {
  manifest,
  sourceCommit: 'ABCDEF0123456789ABCDEF0123456789ABCDEF01',
  generatedAt: '2026-07-16T15:30:00Z',
  runId: '29508551586',
};

const first = createBuildProvenance(input);
const second = createBuildProvenance(input);
assert.strictEqual(serializeBuildProvenance(first), serializeBuildProvenance(second), 'same inputs must be deterministic');
assert.strictEqual(first.source_commit, 'abcdef0123456789abcdef0123456789abcdef01');
assert.strictEqual(first.generated_at, '2026-07-16T15:30:00.000Z');
assert.strictEqual(first.pages_run_url, 'https://github.com/itdojp/formal-methods-book/actions/runs/29508551586');
assert.deepStrictEqual(validateBuildProvenance(first, manifest, { requireRun: true }), []);

for (const [label, replacement, pattern] of [
  ['short SHA', { sourceCommit: 'abcdef0' }, /40-character/],
  ['non-UTC time', { generatedAt: '2026-07-16T15:30:00+09:00' }, /ISO-8601 UTC/],
  ['invalid run ID', { runId: '../secret' }, /positive integer/],
]) {
  assert.throws(() => createBuildProvenance({ ...input, ...replacement }), pattern, label);
}

const withoutRun = createBuildProvenance({ ...input, runId: null });
assert.deepStrictEqual(validateBuildProvenance(withoutRun, manifest), []);
assert(validateBuildProvenance(withoutRun, manifest, { requireRun: true }).includes('pages_run_id is required for a built-site provenance check'));

const tampered = { ...first, source_url: 'https://example.com/commit/abcdef' };
assert(validateBuildProvenance(tampered, manifest).includes('source_url does not match source_commit'));

const wrongVersionManifest = JSON.parse(JSON.stringify(manifest));
wrongVersionManifest.project.version = 'next';
assert.throws(() => createBuildProvenance({ ...input, manifest: wrongVersionManifest }), /MAJOR\.MINOR\.PATCH/);

console.log('Build provenance tests passed (determinism, validation, canonical URLs, CI run contract).');
