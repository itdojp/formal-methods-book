#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  analyzeMarkdown,
  compareTranslationFeatures,
  evaluateTranslationStatus,
  extractMarkdownDestinations,
  insertTranslationNotice,
  sha256,
  validateTranslationManifest,
} = require('./lib/translation-status');

const repoRoot = path.resolve(__dirname, '..');
const testRoot = path.join(repoRoot, 'tools', '.tmp', 'bilingual-integrity-test');
const SOURCE_COMMIT = '1'.repeat(40);
const TRANSLATED_COMMIT = '2'.repeat(40);
const REVIEW_DATE = '2026-07-16';

function test(name, callback) {
  try {
    callback();
    console.log(`PASS: ${name}`);
  } catch (error) {
    console.error(`FAIL: ${name}`);
    throw error;
  }
}

function fixtureModel() {
  return {
    manifest: {
      project: { defaultEdition: 'ja' },
      translation: { statusManifest: 'translation-status.json' },
      editions: {
        ja: { sourceRoot: 'src/ja', sourceOfTruth: true },
        en: { sourceRoot: 'src/en', translationOf: 'ja', sourceOfTruth: false },
      },
    },
    editions: {
      ja: { structure: { chapters: [], appendices: [], specialPages: [] } },
      en: { structure: { chapters: [], appendices: [], specialPages: [] } },
    },
  };
}

function fixtureManifest(source, translation, overrides = {}) {
  return {
    schema_version: '1.0',
    source_locale: 'ja',
    translation_locale: 'en',
    policy: {
      max_sync_age_days: 90,
      partial_stale_release: 'visible-status-and-artifact-required',
      report_path: '.artifacts/translation-status/report.json',
    },
    pages: {
      'index.md': {
        source_path: 'src/ja/index.md',
        translation_path: 'src/en/index.md',
        source_commit: SOURCE_COMMIT,
        translated_commit: TRANSLATED_COMMIT,
        source_sha256: sha256(source),
        translation_sha256: sha256(translation),
        status: 'synced',
        reviewed_at: REVIEW_DATE,
        ...overrides,
      },
    },
  };
}

function evaluate({ source, translation, currentSource = source, currentTranslation = translation, overrides = {} }) {
  fs.rmSync(testRoot, { recursive: true, force: true });
  fs.mkdirSync(path.join(testRoot, 'src', 'ja'), { recursive: true });
  fs.mkdirSync(path.join(testRoot, 'src', 'en'), { recursive: true });
  fs.writeFileSync(path.join(testRoot, 'src', 'ja', 'index.md'), currentSource);
  fs.writeFileSync(path.join(testRoot, 'src', 'en', 'index.md'), currentTranslation);
  const snapshots = new Map([
    [`${SOURCE_COMMIT}:src/ja/index.md`, Buffer.from(source)],
    [`${TRANSLATED_COMMIT}:src/en/index.md`, Buffer.from(translation)],
  ]);
  return evaluateTranslationStatus({
    repoRoot: testRoot,
    publicationModel: fixtureModel(),
    manifest: fixtureManifest(source, translation, overrides),
    now: new Date('2026-07-16T12:00:00Z'),
    readCommitFile: (_root, commit, filePath) => {
      const content = snapshots.get(`${commit}:${filePath}`);
      if (!content) throw new Error('fixture snapshot not found');
      return content;
    },
  });
}

function assertSyncedMismatch(source, translation, dimension) {
  const result = evaluate({ source, translation });
  assert(result.errors.some((message) => message.includes(`synced structure differs: ${dimension}`)), result.errors);
  assert(result.pages[0].mismatches.includes(dimension));
}

try {
  test('manifest requires exact one-to-one page coverage', () => {
    const manifest = fixtureManifest('# Source\n', '# Translation\n');
    delete manifest.pages['index.md'];
    assert(validateTranslationManifest(manifest, fixtureModel()).some((message) => message.includes('missing pages')));
  });

  test('matching tracked page is accepted as synced', () => {
    const result = evaluate({ source: '# Source\n\nBody.\n', translation: '# Translation\n\nBody.\n' });
    assert.deepStrictEqual(result.errors, []);
    assert.strictEqual(result.summary.status_counts.synced, 1);
  });

  test('synced heading structure mismatch fails', () => {
    assertSyncedMismatch('# S\n\n## 1.1 A\n', '# T\n\n### 1.1 A\n', 'heading_structure');
  });

  test('synced code fence language mismatch fails', () => {
    assertSyncedMismatch('# S\n\n```javascript\nx\n```\n', '# T\n\n```typescript\nx\n```\n', 'code_blocks');
  });

  test('synced table shape mismatch fails', () => {
    assertSyncedMismatch(
      '# S\n\n| A | B |\n| --- | --- |\n| 1 | 2 |\n',
      '# T\n\n| A | B | C |\n| --- | --- | --- |\n| 1 | 2 | 3 |\n',
      'tables',
    );
  });

  test('synced strict tool-label mismatch fails', () => {
    assertSyncedMismatch('# S\n\n【擬似記法】\n', '# T\n', 'tool_labels');
  });

  test('localized strict tool labels compare by semantic category', () => {
    const result = evaluate({
      source: '# S\n\n【ツール準拠（そのまま動く）】\n',
      translation: '# T\n\n【Tool-compliant (runs as-is)】\n',
    });
    assert.deepStrictEqual(result.errors, []);
  });

  test('synced example-path mismatch fails', () => {
    assertSyncedMismatch('# S\n\n`examples/a/model.tla`\n', '# T\n\n`examples/b/model.tla`\n', 'example_paths');
  });

  test('synced external-reference mismatch fails', () => {
    assertSyncedMismatch('# S\n\n<https://example.com/a>\n', '# T\n\n<https://example.com/b>\n', 'external_reference_links');
  });

  test('partial structural mismatch warns without failing', () => {
    const result = evaluate({
      source: '# S\n\n## 1.1 A\n',
      translation: '# T\n\n### 1.1 A\n',
      overrides: {
        status: 'partial',
        tracking_issue: 'https://github.com/itdojp/formal-methods-book/issues/328',
        notes: 'Fixture remains partial.',
      },
    });
    assert.deepStrictEqual(result.errors, []);
    assert(result.warnings.some((message) => message.includes('partial translation: heading_structure')));
  });

  test('content drift requires a partial page to become stale or be re-reviewed', () => {
    const result = evaluate({
      source: '# S\n',
      translation: '# T\n',
      currentTranslation: '# T\n\nChanged after review.\n',
      overrides: {
        status: 'partial',
        tracking_issue: 'https://github.com/itdojp/formal-methods-book/issues/328',
        notes: 'Fixture remains partial.',
      },
    });
    assert(result.errors.some((message) => message.includes('mark stale or re-review')));
  });

  test('legacy free-text status header is rejected', () => {
    const text = '# T\n\n> Translation status: draft\n> Japanese source of truth: src/ja/index.md\n';
    const result = evaluate({ source: '# S\n\nBody.\n', translation: text });
    assert(result.errors.some((message) => message.includes('legacy free-text')));
  });

  test('synced review beyond the configured age fails', () => {
    fs.rmSync(testRoot, { recursive: true, force: true });
    const source = '# S\n';
    const translation = '# T\n';
    fs.mkdirSync(path.join(testRoot, 'src', 'ja'), { recursive: true });
    fs.mkdirSync(path.join(testRoot, 'src', 'en'), { recursive: true });
    fs.writeFileSync(path.join(testRoot, 'src', 'ja', 'index.md'), source);
    fs.writeFileSync(path.join(testRoot, 'src', 'en', 'index.md'), translation);
    const result = evaluateTranslationStatus({
      repoRoot: testRoot,
      publicationModel: fixtureModel(),
      manifest: fixtureManifest(source, translation),
      now: new Date('2026-10-15T12:00:00Z'),
      readCommitFile: (_root, commit) => Buffer.from(commit === SOURCE_COMMIT ? source : translation),
    });
    assert(result.errors.some((message) => message.includes('exceeds max_sync_age_days')));
  });

  test('public notice exposes status, source commit, review date, and tracking issue', () => {
    const rendered = insertTranslationNotice('# Title\n\nBody.\n', {
      status: 'partial',
      source_commit: SOURCE_COMMIT,
      reviewed_at: REVIEW_DATE,
      tracking_issue: 'https://github.com/itdojp/formal-methods-book/issues/328',
      translation_path: 'src/en/index.md',
    });
    assert.match(rendered, /Translation status: Partial/);
    assert.match(rendered, /111111111111/);
    assert.match(rendered, /2026-07-16/);
    assert.match(rendered, /issues\/328/);
  });

  test('Markdown destination parser preserves balanced URL parentheses', () => {
    assert.deepStrictEqual(
      extractMarkdownDestinations(
        '[Lustre](https://example.test/Lustre_(language) "title") '
          + 'and [spec](<https://example.test/spec> "title") and <https://example.test/auto>',
      ),
      ['https://example.test/Lustre_(language)', 'https://example.test/spec', 'https://example.test/auto'],
    );
  });

  test('feature comparison has a stable seven-dimension contract', () => {
    const source = analyzeMarkdown(
      '# S\n\n## 1.1 A\n\n```js\nx\n```\n\n| A | B |\n| --- | --- |\n'
        + '\n【擬似記法】\n\n`examples/a.tla`\n\n<https://example.test/a>\n',
    );
    const translation = analyzeMarkdown('# T\n');
    assert.deepStrictEqual(compareTranslationFeatures(source, translation), [
      'heading_structure',
      'numbered_heading_ids',
      'code_blocks',
      'tables',
      'tool_labels',
      'example_paths',
      'external_reference_links',
    ]);
  });
} finally {
  fs.rmSync(testRoot, { recursive: true, force: true });
}

console.log('Bilingual integrity tests passed (16 cases).');
