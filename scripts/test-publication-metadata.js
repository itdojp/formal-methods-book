#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  compareGeneratedArtifacts,
  loadPublicationModel,
  renderGeneratedArtifacts,
  resolveWithinRoot,
  validatePublicationModel,
  writeGeneratedArtifacts,
} = require('./lib/publication-metadata');

const repoRoot = path.resolve(__dirname, '..');
const testRoot = path.join(repoRoot, 'tools', '.tmp', 'publication-metadata-test');

function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

function artifactObject(artifacts) {
  return Object.fromEntries([...artifacts.entries()].sort(([left], [right]) => left.localeCompare(right)));
}

function test(name, callback) {
  try {
    callback();
    console.log(`PASS: ${name}`);
  } catch (error) {
    console.error(`FAIL: ${name}`);
    throw error;
  }
}

const model = loadPublicationModel(repoRoot);

test('current canonical model is valid', () => {
  assert.deepStrictEqual(validatePublicationModel(model), []);
});

test('renderer is deterministic and covers every declared artifact', () => {
  const first = artifactObject(renderGeneratedArtifacts(model));
  const second = artifactObject(renderGeneratedArtifacts(model));
  assert.deepStrictEqual(second, first);
  assert.deepStrictEqual(Object.keys(first), [
    'docs/_config.yml',
    'docs/_data/locales.yml',
    'docs/_data/navigation.yml',
    'docs/_includes/generated/toc-appendices-en.md',
    'docs/_includes/generated/toc-appendices-ja.md',
    'docs/_includes/generated/toc-main-en.md',
    'docs/_includes/generated/toc-main-ja.md',
    'mobile-config.en.json',
    'mobile-config.ja.json',
  ]);
});

test('one canonical title edit updates every dependent surface', () => {
  const changed = clone(model);
  changed.editions.ja.structure.chapters[3].title = '第4章：canonical title fixture';
  const baseline = artifactObject(renderGeneratedArtifacts(model));
  const updated = artifactObject(renderGeneratedArtifacts(changed));
  const changedPaths = Object.keys(baseline).filter((filePath) => baseline[filePath] !== updated[filePath]);
  assert.deepStrictEqual(changedPaths, [
    'docs/_config.yml',
    'docs/_data/navigation.yml',
    'docs/_includes/generated/toc-main-ja.md',
    'mobile-config.ja.json',
  ]);
  for (const filePath of changedPaths) assert.match(updated[filePath], /canonical title fixture/);
});

test('duplicate order and non-canonical path are rejected', () => {
  const invalid = clone(model);
  invalid.editions.ja.structure.chapters[1].order = invalid.editions.ja.structure.chapters[0].order;
  invalid.editions.en.structure.chapters[0].path = '/chapters/chapter01/';
  const errors = validatePublicationModel(invalid);
  assert(errors.some((message) => message.includes('duplicate order')));
  assert(errors.some((message) => message.includes('expected "/en/chapters/chapter01/"')));
});

test('JA and EN inventories and part mappings remain 1:1', () => {
  const invalid = clone(model);
  invalid.editions.en.structure.chapters[0].id = 'chapter99';
  invalid.editions.en.structure.chapters[1].part = 'part-iv';
  const errors = validatePublicationModel(invalid);
  assert(errors.some((message) => message.includes('chapter') && message.includes('ids must match')));
  assert(errors.some((message) => message.includes('chapter part mapping')));
});

test('exact-byte checker detects a stale generated artifact', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const artifacts = renderGeneratedArtifacts(model);
    writeGeneratedArtifacts(testRoot, artifacts);
    assert.deepStrictEqual(compareGeneratedArtifacts(testRoot, artifacts), []);
    fs.appendFileSync(path.join(testRoot, 'docs', '_data', 'navigation.yml'), '# manual drift\n');
    assert.deepStrictEqual(compareGeneratedArtifacts(testRoot, artifacts), [
      'docs/_data/navigation.yml: stale or manually edited generated artifact',
    ]);
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('checker detects an orphaned generated include', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const artifacts = renderGeneratedArtifacts(model);
    writeGeneratedArtifacts(testRoot, artifacts);
    fs.writeFileSync(path.join(testRoot, 'docs', '_includes', 'generated', 'orphan.md'), 'stale\n');
    assert.deepStrictEqual(compareGeneratedArtifacts(testRoot, artifacts), [
      'docs/_includes/generated/orphan.md: unexpected generated artifact',
    ]);
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('checker detects removed top-level and data artifacts by generated marker', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const artifacts = renderGeneratedArtifacts(model);
    writeGeneratedArtifacts(testRoot, artifacts);
    const reducedArtifacts = new Map(artifacts);
    reducedArtifacts.delete('mobile-config.en.json');
    reducedArtifacts.delete('docs/_data/locales.yml');
    assert.deepStrictEqual(
      new Set(compareGeneratedArtifacts(testRoot, reducedArtifacts)),
      new Set([
        'mobile-config.en.json: unexpected generated artifact',
        'docs/_data/locales.yml: unexpected generated artifact',
      ]),
    );
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('repository paths cannot escape or redirect destructive build roots', () => {
  assert.throws(() => resolveWithinRoot(repoRoot, '../escape.json', 'fixture'), /escapes repository root/);
  assert.throws(() => resolveWithinRoot(repoRoot, '/absolute.json', 'fixture'), /repository-relative path/);
  const invalid = clone(model);
  invalid.manifest.editions.en.publishRoot = '.';
  invalid.manifest.editions.en.mobileConfig = '../mobile.json';
  const errors = validatePublicationModel(invalid);
  assert(errors.some((message) => message.includes('editions.en.publishRoot')));
  assert(errors.some((message) => message.includes('editions.en.mobileConfig')));
});

test('exactly the default edition is the source of truth', () => {
  const invalid = clone(model);
  invalid.manifest.editions.en.sourceOfTruth = true;
  invalid.manifest.editions.en.translationOf = 'fr';
  invalid.editions.en.edition.sourceOfTruth = true;
  invalid.editions.en.edition.translationOf = 'fr';
  invalid.editions.en.edition.label = 'Bad label';
  const errors = validatePublicationModel(invalid);
  assert(errors.some((message) => message.includes('editions.en.sourceOfTruth must be false')));
  assert(errors.some((message) => message.includes('editions.en.translationOf must be "ja"')));
  assert(errors.some((message) => message.includes('edition.sourceOfTruth must be false')));
  assert(errors.some((message) => message.includes('edition.translationOf must be "ja"')));
  assert(errors.some((message) => message.includes('edition.label must match manifest edition')));
});

console.log('Publication metadata renderer tests passed (10 cases).');
