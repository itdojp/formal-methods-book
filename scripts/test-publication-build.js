#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  compareEditionPages,
  renderEditionPages,
  renderPublicationPage,
  writeEditionPages,
} = require('./lib/publication-build');

const repoRoot = path.resolve(__dirname, '..');
const testRoot = path.join(repoRoot, 'tools', '.tmp', 'publication-build-test');
const outsideRoot = path.join(repoRoot, 'tools', '.tmp', 'publication-build-outside');

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
      editions: {
        ja: { sourceRoot: 'src/ja', publishRoot: 'docs' },
        en: { sourceRoot: 'src/en', publishRoot: 'docs/en' },
      },
    },
  };
}

test('JA renderer adds canonical front matter and rewrites source asset links', () => {
  const outputFile = path.join(repoRoot, 'docs', 'chapters', 'chapter01', 'index.md');
  const rendered = renderPublicationPage({
    content: '# 第1章\n\n![図](../../../docs/assets/images/diagram.svg)\n',
    locale: 'ja',
    metadata: { title: '第1章', description: '説明' },
    outputFile,
    repoRoot,
    sourcePath: 'src/ja/chapters/chapter01.md',
  });
  assert.match(rendered, /locale: "ja"\nlang: "ja"\nsource_path: "src\/ja\/chapters\/chapter01\.md"/);
  assert.match(rendered, /!\[図\]\(\.\.\/\.\.\/assets\/images\/diagram\.svg\)/);
});

test('EN renderer publishes machine-readable and visible translation status', () => {
  const rendered = renderPublicationPage({
    content: '# Chapter 1\n\nBody.\n',
    locale: 'en',
    metadata: { title: 'Chapter 1' },
    outputFile: path.join(repoRoot, 'docs', 'en', 'chapters', 'chapter01', 'index.md'),
    repoRoot,
    sourcePath: 'src/en/chapters/chapter01.md',
    translationStatus: {
      status: 'partial',
      source_commit: '0123456789abcdef0123456789abcdef01234567',
      reviewed_at: '2026-07-16',
      tracking_issue: 'https://github.com/itdojp/formal-methods-book/issues/328',
      translation_path: 'src/en/chapters/chapter01.md',
    },
  });
  assert.match(rendered, /translation_status: "partial"/);
  assert.match(rendered, /translation_source_commit: "0123456789abcdef0123456789abcdef01234567"/);
  assert.match(rendered, /translation_reviewed_at: "2026-07-16"/);
  assert.match(rendered, /translation_tracking_issue: "https:\/\/github\.com\/itdojp\/formal-methods-book\/issues\/328"/);
  assert.match(rendered, /# Chapter 1\n\n> \*\*Translation status: Partial\.\*\*/);
  assert.match(rendered, /# Chapter 1[\s\S]*Body\./);
});

test('renderer rewrites canonical example links to the current Pages revision', () => {
  const rendered = renderPublicationPage({
    content: '# Chapter\n\n[examples/tool/model.txt](../../../examples/tool/model.txt)\n',
    locale: 'ja',
    metadata: { title: 'Chapter' },
    outputFile: path.join(repoRoot, 'docs', 'chapters', 'chapter', 'index.md'),
    repoRoot,
    sourcePath: 'src/ja/chapters/chapter.md',
  });
  assert.match(
    rendered,
    /https:\/\/github\.com\/itdojp\/formal-methods-book\/blob\/\{\{site\.github\.build_revision\|default:'main'\}\}\/examples\/tool\/model\.txt/,
  );
});

test('renderer is byte-for-byte deterministic', () => {
  const input = {
    content: '# Chapter\n\nBody.\n',
    locale: 'ja',
    metadata: { title: 'Chapter', description: 'Description' },
    outputFile: path.join(repoRoot, 'docs', 'chapters', 'chapter', 'index.md'),
    repoRoot,
    sourcePath: 'src/ja/chapters/chapter.md',
  };
  assert.strictEqual(renderPublicationPage(input), renderPublicationPage(input));
});

test('writer removes stale generated Markdown but preserves unmanaged files and nested editions', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const model = fixtureModel();
    const pages = new Map([
      ['docs/index.md', '---\nsource_path: "src/ja/index.md"\n---\n# Home\n'],
    ]);
    fs.mkdirSync(path.join(testRoot, 'docs', 'old'), { recursive: true });
    fs.mkdirSync(path.join(testRoot, 'docs', 'assets'), { recursive: true });
    fs.mkdirSync(path.join(testRoot, 'docs', 'en'), { recursive: true });
    fs.writeFileSync(path.join(testRoot, 'docs', 'old', 'index.md'), '---\nsource_path: "src/ja/old.md"\n---\n# Old\n');
    fs.writeFileSync(path.join(testRoot, 'docs', 'README.md'), '# Unmanaged\n');
    fs.writeFileSync(path.join(testRoot, 'docs', 'assets', 'diagram.svg'), '<svg/>\n');
    fs.writeFileSync(path.join(testRoot, 'docs', 'en', 'index.md'), '---\nsource_path: "src/en/index.md"\n---\n# EN\n');

    writeEditionPages(testRoot, model, 'ja', pages);

    assert(!fs.existsSync(path.join(testRoot, 'docs', 'old', 'index.md')));
    assert(fs.existsSync(path.join(testRoot, 'docs', 'README.md')));
    assert(fs.existsSync(path.join(testRoot, 'docs', 'assets', 'diagram.svg')));
    assert(fs.existsSync(path.join(testRoot, 'docs', 'en', 'index.md')));
    assert.strictEqual(fs.readFileSync(path.join(testRoot, 'docs', 'index.md'), 'utf8'), pages.get('docs/index.md'));
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('exact checker detects direct docs edits and orphaned generated pages', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const model = fixtureModel();
    const pages = new Map([
      ['docs/index.md', '---\nsource_path: "src/ja/index.md"\n---\n# Home\n'],
    ]);
    writeEditionPages(testRoot, model, 'ja', pages);
    fs.appendFileSync(path.join(testRoot, 'docs', 'index.md'), 'manual edit\n');
    fs.mkdirSync(path.join(testRoot, 'docs', 'stale'), { recursive: true });
    fs.writeFileSync(
      path.join(testRoot, 'docs', 'stale', 'index.md'),
      '---\nsource_path: "src/ja/stale.md"\n---\n# Stale\n',
    );
    assert.deepStrictEqual(compareEditionPages(testRoot, model, 'ja', pages), [
      'docs/index.md: stale or manually edited generated publication page',
      'docs/stale/index.md: unexpected generated publication page',
    ]);
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('edition renderer rejects source Markdown without a canonical mapping', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const model = fixtureModel();
    model.editions = {
      ja: { title: 'JA', description: 'JA', structure: { chapters: [], appendices: [], specialPages: [] } },
    };
    fs.mkdirSync(path.join(testRoot, 'src', 'ja'), { recursive: true });
    fs.writeFileSync(path.join(testRoot, 'src', 'ja', 'index.md'), '# JA\n');
    fs.writeFileSync(path.join(testRoot, 'src', 'ja', 'unmapped.md'), '# Unmapped\n');
    assert.throws(
      () => renderEditionPages(testRoot, model, 'ja'),
      /source file has no publication mapping: unmapped\.md/,
    );
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('edition renderer rejects a declared page without a canonical source file', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  try {
    const model = fixtureModel();
    model.editions = {
      ja: {
        title: 'JA',
        description: 'JA',
        structure: {
          chapters: [{ id: 'chapter01', title: 'Chapter 1' }],
          appendices: [],
          specialPages: [],
        },
      },
    };
    fs.mkdirSync(path.join(testRoot, 'src', 'ja'), { recursive: true });
    fs.writeFileSync(path.join(testRoot, 'src', 'ja', 'index.md'), '# JA\n');
    assert.throws(
      () => renderEditionPages(testRoot, model, 'ja'),
      /expected 2 declared publication pages, rendered 1/,
    );
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
  }
});

test('writer rejects a symlinked publish root without modifying its target', () => {
  fs.rmSync(testRoot, { recursive: true, force: true });
  fs.rmSync(outsideRoot, { recursive: true, force: true });
  try {
    const model = fixtureModel();
    const pages = new Map([
      ['docs/index.md', '---\nsource_path: "src/ja/index.md"\n---\n# Home\n'],
    ]);
    fs.mkdirSync(testRoot, { recursive: true });
    fs.mkdirSync(outsideRoot, { recursive: true });
    fs.writeFileSync(path.join(outsideRoot, 'sentinel.txt'), 'unchanged\n');
    fs.symlinkSync(outsideRoot, path.join(testRoot, 'docs'), 'dir');
    assert.throws(
      () => writeEditionPages(testRoot, model, 'ja', pages),
      /symbolic link path component is not allowed: docs/,
    );
    assert.strictEqual(fs.readFileSync(path.join(outsideRoot, 'sentinel.txt'), 'utf8'), 'unchanged\n');
    assert(!fs.existsSync(path.join(outsideRoot, 'index.md')));
  } finally {
    fs.rmSync(testRoot, { recursive: true, force: true });
    fs.rmSync(outsideRoot, { recursive: true, force: true });
  }
});

console.log('Publication build tests passed (9 cases).');
