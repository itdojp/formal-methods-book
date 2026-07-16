#!/usr/bin/env node
'use strict';

const assert = require('assert');
const path = require('path');
const {
  createBuildProvenance,
  detectReleaseTag,
  readJson,
  sameJsonValue,
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
  releaseTag: 'v1.1.0',
};

const first = createBuildProvenance(input);
const second = createBuildProvenance(input);
assert.strictEqual(serializeBuildProvenance(first), serializeBuildProvenance(second), 'same inputs must be deterministic');
assert.strictEqual(first.source_commit, 'abcdef0123456789abcdef0123456789abcdef01');
assert.strictEqual(first.generated_at, '2026-07-16T15:30:00.000Z');
assert.strictEqual(first.pages_run_url, 'https://github.com/itdojp/formal-methods-book/actions/runs/29508551586');
assert.strictEqual(first.release_url, 'https://github.com/itdojp/formal-methods-book/releases/tag/v1.1.0');
assert.deepStrictEqual(validateBuildProvenance(first, manifest, { requireRun: true }), []);
assert.deepStrictEqual(validateBuildProvenance(first, manifest, {
  requireRun: true,
  repoRoot,
  execute: () => `${input.sourceCommit}\n`,
}), []);
assert(validateBuildProvenance(first, manifest, {
  repoRoot,
  execute: () => '1111111111111111111111111111111111111111\n',
}).includes('release_tag v1.1.0 does not resolve to source_commit'));

const detected = detectReleaseTag(repoRoot, manifest, input.sourceCommit, () => `${input.sourceCommit}\n`);
assert.strictEqual(detected, 'v1.1.0', 'exact version tag target must mark a release build');
const notAtSource = detectReleaseTag(repoRoot, manifest, input.sourceCommit, () => '1111111111111111111111111111111111111111\n');
assert.strictEqual(notAtSource, null, 'tag at another commit must not mark a release build');
const missingTag = detectReleaseTag(repoRoot, manifest, input.sourceCommit, () => { throw new Error('missing tag'); });
assert.strictEqual(missingTag, null, 'missing tag must produce a non-release build');

const reordered = Object.fromEntries(Object.entries(first).reverse());
assert(sameJsonValue(first, reordered), 'semantic JSON comparison must ignore object key order');
assert(!sameJsonValue(first, { ...reordered, version: '9.9.9' }), 'semantic JSON comparison must detect changed values');

const repositoryWithoutGit = JSON.parse(JSON.stringify(manifest));
repositoryWithoutGit.repository.url = 'https://github.com/itdojp/formal-methods-book';
assert.doesNotThrow(() => createBuildProvenance({ ...input, manifest: repositoryWithoutGit }));
const repositoryWithGitAndSlash = JSON.parse(JSON.stringify(manifest));
repositoryWithGitAndSlash.repository.url = 'https://github.com/itdojp/formal-methods-book.git/';
assert.doesNotThrow(() => createBuildProvenance({ ...input, manifest: repositoryWithGitAndSlash }));
const wrongRepository = JSON.parse(JSON.stringify(manifest));
wrongRepository.repository.url = 'https://github.com/itdojp/other-book.git';
assert.throws(() => createBuildProvenance({ ...input, manifest: wrongRepository }), /optional \.git suffix/);

for (const [label, replacement, pattern] of [
  ['short SHA', { sourceCommit: 'abcdef0' }, /40-character/],
  ['non-UTC time', { generatedAt: '2026-07-16T15:30:00+09:00' }, /ISO-8601 UTC/],
  ['invalid run ID', { runId: '../secret' }, /positive integer/],
  ['wrong release tag', { releaseTag: 'v9.9.9' }, /release tag must be v1\.1\.0/],
]) {
  assert.throws(() => createBuildProvenance({ ...input, ...replacement }), pattern, label);
}

const withoutRun = createBuildProvenance({ ...input, runId: null });
assert.deepStrictEqual(validateBuildProvenance(withoutRun, manifest), []);
assert(validateBuildProvenance(withoutRun, manifest, { requireRun: true }).includes('pages_run_id is required for a built-site provenance check'));

const nonRelease = createBuildProvenance({ ...input, releaseTag: null });
assert.strictEqual(nonRelease.release_tag, null);
assert.strictEqual(nonRelease.release_url, null);
assert.deepStrictEqual(validateBuildProvenance(nonRelease, manifest), []);
assert(validateBuildProvenance(nonRelease, manifest, {
  repoRoot,
  execute: () => `${input.sourceCommit}\n`,
}).includes('release_tag must be v1.1.0 when that tag resolves to source_commit'));
assert(validateBuildProvenance({ ...nonRelease, release_url: first.release_url }, manifest)
  .includes('release_url must be null when release_tag is null'));

const tampered = { ...first, source_url: 'https://example.com/commit/abcdef' };
assert(validateBuildProvenance(tampered, manifest).includes('source_url does not match source_commit'));
assert(validateBuildProvenance({ ...first, source_commit: 'abcdef0' }, manifest, {
  repoRoot,
  execute: () => `${input.sourceCommit}\n`,
}).includes('source commit must be a full 40-character hexadecimal SHA'));

const wrongVersionManifest = JSON.parse(JSON.stringify(manifest));
wrongVersionManifest.project.version = 'next';
assert.throws(() => createBuildProvenance({ ...input, manifest: wrongVersionManifest }), /MAJOR\.MINOR\.PATCH/);

console.log('Build provenance tests passed (determinism, validation, canonical URLs, CI run contract).');
