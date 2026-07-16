#!/usr/bin/env node
'use strict';

const path = require('path');
const { execFileSync } = require('child_process');
const {
  createBuildProvenance,
  detectReleaseTag,
  readJson,
  writeBuildProvenance,
} = require('./lib/build-provenance');

if (process.argv.length !== 2) {
  console.error('Usage: node scripts/generate-build-provenance.js');
  process.exit(2);
}

const repoRoot = path.resolve(__dirname, '..');

function currentCommit() {
  return execFileSync('git', ['rev-parse', 'HEAD'], {
    cwd: repoRoot,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'inherit'],
  }).trim();
}

try {
  const manifest = readJson(path.join(repoRoot, 'book-config.json'));
  const sourceCommit = currentCommit();
  const payload = createBuildProvenance({
    manifest,
    sourceCommit,
    generatedAt: process.env.BOOK_GENERATED_AT || new Date().toISOString(),
    runId: process.env.GITHUB_RUN_ID || null,
    releaseTag: detectReleaseTag(repoRoot, manifest, sourceCommit),
  });
  const outputPath = writeBuildProvenance(repoRoot, payload);
  console.log(`Generated ${path.relative(repoRoot, outputPath)} for ${payload.version} at ${payload.source_commit}.`);
} catch (error) {
  console.error(error.message);
  process.exit(1);
}
