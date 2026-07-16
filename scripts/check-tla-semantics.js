#!/usr/bin/env node
'use strict';

const fs = require('fs');
const assert = require('assert');

const errors = [];

function read(filePath) {
  return fs.readFileSync(filePath, 'utf8').replace(/\r\n/g, '\n');
}

function lineOf(content, needle) {
  const index = content.indexOf(needle);
  if (index < 0) return 1;
  return content.slice(0, index).split('\n').length;
}

function report(filePath, content, needle, message) {
  errors.push({ filePath, line: lineOf(content, needle), message });
}

function requireText(filePath, needles) {
  const content = read(filePath);
  for (const needle of needles) {
    if (!content.includes(needle)) {
      report(filePath, content, needle, `required TLA+ semantic marker is missing: ${needle}`);
    }
  }
}

function forbidText(filePath, needles) {
  const content = read(filePath);
  for (const needle of needles) {
    if (content.includes(needle)) {
      report(filePath, content, needle, `obsolete or misleading TLA+ marker remains: ${needle}`);
    }
  }
}

const toolCompliantLabels = [
  '【ツール準拠（そのまま動く）】',
  '〖ツール準拠（そのまま動く）〗',
  '【Tool-compliant (runs as-is)】',
  '〖Tool-compliant (runs as-is)〗',
];

function findToolCompliantFairness(content) {
  const lines = content.split('\n');
  for (let index = 0; index < lines.length - 1; index += 1) {
    if (!toolCompliantLabels.includes(lines[index].trim())) continue;

    const openingFence = lines[index + 1].trim();
    if (!openingFence.startsWith('```')) continue;
    const language = openingFence.slice(3).trim().toLowerCase();
    if (language !== 'tla') continue;

    const blockLines = [];
    let closingIndex = index + 2;
    for (; closingIndex < lines.length; closingIndex += 1) {
      if (lines[closingIndex].trim() === '```') break;
      blockLines.push(lines[closingIndex]);
    }
    if (/\b(?:WF|SF)_vars\s*\(/u.test(blockLines.join('\n'))) {
      return lines.slice(index, Math.min(closingIndex + 1, lines.length)).join('\n');
    }
  }
  return null;
}

function forbidToolCompliantFairness(filePath) {
  const content = read(filePath);
  const match = findToolCompliantFairness(content);
  if (match) {
    report(
      filePath,
      content,
      match,
      'WF/SF blocks in Chapter 7 must remain context-dependent unless a complete verified example and guard are added',
    );
  }
}

function stripFrontMatter(content) {
  if (!content.startsWith('---\n')) return content;
  const end = content.indexOf('\n---\n', 4);
  return end < 0 ? content : content.slice(end + 5);
}

function stripEnglishTranslationMetadata(content) {
  return content.replace(
    /(^# [^\n]+\n\n)> Translation status:[^\n]*\n> Japanese source of truth:[^\n]*\n\n/,
    '$1',
  );
}

function normalizeBody(content) {
  return content.replace(/\r\n/g, '\n').trimEnd();
}

function requireGeneratedMatch(sourcePath, publicPath, locale) {
  let source = read(sourcePath);
  if (locale === 'en') {
    source = stripEnglishTranslationMetadata(source);
  }
  const published = stripFrontMatter(read(publicPath));
  if (normalizeBody(source) !== normalizeBody(published)) {
    errors.push({
      filePath: publicPath,
      line: 1,
      message: `${publicPath} is stale; run npm run build:all after updating ${sourcePath}`,
    });
  }
}

function runSelfTest() {
  assert.strictEqual(stripFrontMatter('---\ntitle: T\n---\nBody\n'), 'Body\n');
  assert.strictEqual(stripFrontMatter('Body\n'), 'Body\n');
  assert.strictEqual(
    stripEnglishTranslationMetadata(
      '# Chapter\n\n> Translation status: synchronized\n' +
        '> Japanese source of truth: `src/ja/chapter.md`\n\nBody\n',
    ),
    '# Chapter\n\nBody\n',
  );

  for (const [labelIndex, label] of toolCompliantLabels.entries()) {
    const fence = labelIndex % 2 === 0 ? '```tla' : '  ``` TLA  ';
    const incomplete = `  ${label}  \n${fence}\nSpec == Init /\\ [][Next]_vars\n` +
      '        /\\ WF_vars(Action)\n  ```';
    assert(findToolCompliantFairness(incomplete));
  }

  assert.strictEqual(
    findToolCompliantFairness(
      '【Context-dependent snippet】\n\`\`\`tla\nWF_vars(Action)\n\`\`\`',
    ),
    null,
  );
  assert.strictEqual(
    findToolCompliantFairness(
      '【Tool-compliant (runs as-is)】\n\`\`\`text\nWF_vars(Action)\n\`\`\`',
    ),
    null,
  );
  console.log('OK: TLA+ semantic checker self-tests passed.');
}

if (process.argv.includes('--self-test')) {
  runSelfTest();
  process.exit(0);
}

const japaneseChapters = [
  'src/ja/chapters/chapter07.md',
  'docs/chapters/chapter07/index.md',
];
const englishChapters = [
  'src/en/chapters/chapter07.md',
  'docs/en/chapters/chapter07/index.md',
];

for (const filePath of japaneseChapters) {
  requireText(filePath, [
    '`P ~> Q`（leads-to）',
    'LTL の `X P`',
    '時相論理の next-time 演算子ではありません',
    '【文脈依存スニペット】\n```tla\nSpec == Init /\\ [][Next]_vars',
    'ConcreteSpec => AbstractSpec',
    'refinement mapping',
  ]);
  forbidText(filePath, [
    '**○ (Next',
    '抽象仕様 ⊨ 具体仕様',
  ]);
  forbidToolCompliantFairness(filePath);
}

for (const filePath of englishChapters) {
  requireText(filePath, [
    '`P ~> Q` (leads-to)',
    'The LTL formula `X P`',
    'TLA+ prime notation is different',
    '【Context-dependent snippet】\n```tla\nSpec == Init /\\ [][Next]_vars',
    'ConcreteSpec => AbstractSpec',
    'refinement mapping',
  ]);
  forbidText(filePath, [
    '**`○` (next)**',
    'abstract specification ⊨ concrete specification',
  ]);
  forbidToolCompliantFairness(filePath);
}

requireText('src/ja/appendices/appendix-c.md', [
  'ConcreteSpec => AbstractSpec',
  '`P ~> Q`',
  'LTL の `X` / `○` とは別',
]);
requireText('src/en/appendices/appendix-c.md', [
  'ConcreteSpec => AbstractSpec',
  '`P ~> Q`',
  'distinct from LTL `X` / `○`',
]);
requireText('src/ja/glossary/index.md', [
  '**プライム記法（TLA+）**',
  '**refinement（詳細化）**',
  'ConcreteSpec => AbstractSpec',
]);
requireText('src/en/glossary/index.md', [
  '**Prime notation (TLA+)**',
  '**Refinement**',
  'ConcreteSpec => AbstractSpec',
]);

const primarySourceUrls = [
  'https://lamport.azurewebsites.net/tla/tla2.html',
  'https://lamport.azurewebsites.net/tla/book.html',
  'https://lamport.azurewebsites.net/tla/hyperbook.html',
];
requireText('src/ja/appendices/appendix-e.md', primarySourceUrls);
requireText('src/en/appendices/appendix-e.md', primarySourceUrls);

// English chapters and both locales' generated appendices/glossaries are exact
// build outputs. Japanese chapter pages are hand-maintained and may contain
// public-only navigation, so their Issue #313 semantic claims are guarded above
// without asserting byte-for-byte body equality.
for (const [sourcePath, publicPath, locale] of [
  ['src/ja/appendices/appendix-c.md', 'docs/appendices/appendix-c/index.md', 'ja'],
  ['src/ja/appendices/appendix-e.md', 'docs/appendices/appendix-e/index.md', 'ja'],
  ['src/ja/glossary/index.md', 'docs/glossary/index.md', 'ja'],
  ['src/en/chapters/chapter07.md', 'docs/en/chapters/chapter07/index.md', 'en'],
  ['src/en/appendices/appendix-c.md', 'docs/en/appendices/appendix-c/index.md', 'en'],
  ['src/en/appendices/appendix-e.md', 'docs/en/appendices/appendix-e/index.md', 'en'],
  ['src/en/glossary/index.md', 'docs/en/glossary/index.md', 'en'],
]) {
  requireGeneratedMatch(sourcePath, publicPath, locale);
}

if (errors.length > 0) {
  for (const error of errors) {
    const message = String(error.message).replace(/\r?\n/g, ' ');
    console.error(`::error file=${error.filePath},line=${error.line}::${message}`);
  }
  console.error(`Found ${errors.length} TLA+ semantic contract error(s).`);
  process.exitCode = 1;
} else {
  console.log('OK: TLA+ next/prime, refinement, fairness, source, and publish contracts match.');
}
