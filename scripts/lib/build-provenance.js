'use strict';

const fs = require('fs');
const path = require('path');
const { isDeepStrictEqual } = require('util');

const SCHEMA_VERSION = '1.0';
const REPOSITORY = 'itdojp/formal-methods-book';
const GITHUB_URL = `https://github.com/${REPOSITORY}`;
const DEFAULT_OUTPUT = 'docs/_data/build_provenance.json';

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function normalizeCommit(value) {
  const commit = String(value || '').trim().toLowerCase();
  if (!/^[0-9a-f]{40}$/.test(commit)) {
    throw new Error('source commit must be a full 40-character hexadecimal SHA');
  }
  return commit;
}

function normalizeGeneratedAt(value) {
  const raw = String(value || '').trim();
  if (!/^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d{1,3})?Z$/.test(raw)) {
    throw new Error('generated-at must be an ISO-8601 UTC timestamp');
  }
  const parsed = new Date(raw);
  if (Number.isNaN(parsed.getTime())) {
    throw new Error('generated-at must be a valid timestamp');
  }
  return parsed.toISOString();
}

function normalizeRunId(value) {
  const runId = String(value || '').trim();
  if (!runId) return null;
  if (!/^[1-9][0-9]*$/.test(runId)) {
    throw new Error('GitHub Actions run ID must be a positive integer');
  }
  return runId;
}

function canonicalVersion(manifest) {
  const version = manifest?.project?.version;
  if (typeof version !== 'string' || !/^\d+\.\d+\.\d+$/.test(version)) {
    throw new Error('book-config.json project.version must use MAJOR.MINOR.PATCH');
  }
  return version;
}

function assertRepository(manifest) {
  const raw = String(manifest?.repository?.url || '').trim().replace(/\.git$/, '').replace(/\/+$/, '');
  if (raw !== GITHUB_URL) {
    throw new Error(`book-config.json repository.url must be ${GITHUB_URL} with an optional .git suffix`);
  }
}

function sameJsonValue(left, right) {
  return isDeepStrictEqual(left, right);
}

function createBuildProvenance({ manifest, sourceCommit, generatedAt, runId }) {
  assertRepository(manifest);
  const version = canonicalVersion(manifest);
  const commit = normalizeCommit(sourceCommit);
  const timestamp = normalizeGeneratedAt(generatedAt);
  const normalizedRunId = normalizeRunId(runId);
  const releaseTag = `v${version}`;

  return {
    schema_version: SCHEMA_VERSION,
    book_id: manifest.project.id,
    version,
    release_tag: releaseTag,
    release_url: `${GITHUB_URL}/releases/tag/${releaseTag}`,
    source_commit: commit,
    source_url: `${GITHUB_URL}/commit/${commit}`,
    generated_at: timestamp,
    pages_run_id: normalizedRunId,
    pages_run_url: normalizedRunId
      ? `${GITHUB_URL}/actions/runs/${normalizedRunId}`
      : null,
  };
}

function validateBuildProvenance(payload, manifest, { requireRun = false } = {}) {
  const errors = [];
  let expectedVersion = '';
  try {
    assertRepository(manifest);
    expectedVersion = canonicalVersion(manifest);
  } catch (error) {
    errors.push(error.message);
    return errors;
  }

  if (!payload || typeof payload !== 'object' || Array.isArray(payload)) {
    return ['build provenance must be a JSON object'];
  }
  if (payload.schema_version !== SCHEMA_VERSION) errors.push(`schema_version must be ${SCHEMA_VERSION}`);
  if (payload.book_id !== manifest.project.id) errors.push(`book_id must be ${manifest.project.id}`);
  if (payload.version !== expectedVersion) errors.push(`version must be ${expectedVersion}`);

  const expectedTag = `v${expectedVersion}`;
  if (payload.release_tag !== expectedTag) errors.push(`release_tag must be ${expectedTag}`);
  if (payload.release_url !== `${GITHUB_URL}/releases/tag/${expectedTag}`) errors.push('release_url is not canonical');

  try {
    const commit = normalizeCommit(payload.source_commit);
    if (payload.source_url !== `${GITHUB_URL}/commit/${commit}`) errors.push('source_url does not match source_commit');
  } catch (error) {
    errors.push(error.message);
  }

  try {
    const generatedAt = normalizeGeneratedAt(payload.generated_at);
    if (payload.generated_at !== generatedAt) errors.push('generated_at must use canonical millisecond UTC form');
  } catch (error) {
    errors.push(error.message);
  }

  let runId = null;
  try {
    runId = normalizeRunId(payload.pages_run_id);
  } catch (error) {
    errors.push(error.message);
  }
  if (requireRun && !runId) errors.push('pages_run_id is required for a built-site provenance check');
  const expectedRunUrl = runId ? `${GITHUB_URL}/actions/runs/${runId}` : null;
  if (payload.pages_run_url !== expectedRunUrl) errors.push('pages_run_url does not match pages_run_id');

  return errors;
}

function serializeBuildProvenance(payload) {
  return `${JSON.stringify(payload, null, 2)}\n`;
}

function writeBuildProvenance(repoRoot, payload) {
  const outputPath = path.join(repoRoot, DEFAULT_OUTPUT);
  fs.mkdirSync(path.dirname(outputPath), { recursive: true });
  const temporaryPath = `${outputPath}.tmp-${process.pid}`;
  fs.writeFileSync(temporaryPath, serializeBuildProvenance(payload), { encoding: 'utf8', mode: 0o644 });
  fs.renameSync(temporaryPath, outputPath);
  return outputPath;
}

module.exports = {
  DEFAULT_OUTPUT,
  GITHUB_URL,
  REPOSITORY,
  SCHEMA_VERSION,
  canonicalVersion,
  createBuildProvenance,
  normalizeCommit,
  normalizeGeneratedAt,
  normalizeRunId,
  readJson,
  sameJsonValue,
  serializeBuildProvenance,
  validateBuildProvenance,
  writeBuildProvenance,
};
