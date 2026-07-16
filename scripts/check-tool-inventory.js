#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { loadManifest, validateManifest } = require('./example-manifest');
const { loadToolManifest, validateToolManifest } = require('./tool-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');
const START = '<!-- tool-inventory:start -->';
const END = '<!-- tool-inventory:end -->';
const SOURCE_FILES = {
  ja: 'src/ja/appendices/appendix-b.md',
  en: 'src/en/appendices/appendix-b.md',
};
const LANE_LABELS = {
  ja: {
    'pr-quick': 'pr-quick',
    nightly: 'nightly',
    optional: 'optional/manual',
    manual: 'manual',
    'documentation-only': 'documentation-only',
  },
  en: {
    'pr-quick': 'pr-quick',
    nightly: 'nightly',
    optional: 'optional/manual',
    manual: 'manual',
    'documentation-only': 'documentation-only',
  },
};

function escapeCell(value) {
  return String(value).replaceAll('|', '\\|').replaceAll('\n', ' ');
}

function renderInventory(manifest, locale) {
  const header = locale === 'ja'
    ? ['Tool / service', 'lane', '検証済み version', '分類理由']
    : ['Tool / service', 'lane', 'Verified version', 'Rationale'];
  const lines = [
    START,
    `| ${header.join(' | ')} |`,
    '| --- | --- | --- | --- |',
  ];
  for (const tool of manifest.tools) {
    lines.push(`| ${[
      tool.name,
      LANE_LABELS[locale][tool.lane],
      tool.version || '—',
      tool.reason[locale],
    ].map(escapeCell).join(' | ')} |`);
  }
  lines.push(END);
  return lines.join('\n');
}

function replaceInventory(content, rendered, filePath) {
  const start = content.indexOf(START);
  const end = content.indexOf(END);
  if (start < 0 || end < 0 || end < start) throw new Error(`${filePath}: inventory markers are missing or reversed`);
  if (content.indexOf(START, start + START.length) >= 0 || content.indexOf(END, end + END.length) >= 0) {
    throw new Error(`${filePath}: inventory markers must occur exactly once`);
  }
  return `${content.slice(0, start)}${rendered}${content.slice(end + END.length)}`;
}

function canonicalJapaneseReaderFiles(rootDir) {
  const config = JSON.parse(fs.readFileSync(path.join(rootDir, 'book-config.ja.json'), 'utf8'));
  const files = ['src/ja/index.md'];
  for (const chapter of config.structure.chapters) files.push(`src/ja/chapters/${chapter.id}.md`);
  for (const appendix of config.structure.appendices) files.push(`src/ja/appendices/${appendix.id}.md`);
  const specialMapping = {
    introduction: 'src/ja/introduction/index.md',
    glossary: 'src/ja/glossary/index.md',
    afterword: 'src/ja/afterword/index.md',
  };
  for (const page of config.structure.specialPages) files.push(specialMapping[page.id]);
  return files;
}

function withoutGeneratedInventory(content) {
  const start = content.indexOf(START);
  const end = content.indexOf(END);
  if (start < 0 || end < start) return content;
  return `${content.slice(0, start)}${content.slice(end + END.length)}`;
}

function validateInventory(rootDir, options = {}) {
  const errors = [];
  const { manifest: toolManifest, manifestPath } = loadToolManifest(rootDir);
  errors.push(...validateToolManifest(toolManifest, { rootDir, manifestPath }).map((error) => error.message));
  const { manifest: exampleManifest, manifestPath: examplePath } = loadManifest(rootDir);
  errors.push(...validateManifest(exampleManifest, {
    rootDir,
    manifestPath: examplePath,
    toolManifest,
  }).map((error) => error.message));

  const examplesByTool = new Map();
  for (const entry of exampleManifest.examples || []) {
    const entries = examplesByTool.get(entry.tool) || [];
    entries.push(entry);
    examplesByTool.set(entry.tool, entries);
  }
  for (const tool of toolManifest.tools) {
    const entries = examplesByTool.get(tool.id) || [];
    if (tool.lane === 'documentation-only' && entries.length > 0) {
      errors.push(`[${tool.id}] documentation-only tool cannot have executable examples`);
    }
    if (tool.lane !== 'documentation-only' && entries.length === 0) {
      errors.push(`[${tool.id}] executable lane ${tool.lane} requires at least one example`);
    }
  }

  const readers = canonicalJapaneseReaderFiles(rootDir);
  const corpus = readers
    .map((file) => withoutGeneratedInventory(fs.readFileSync(path.join(rootDir, file), 'utf8')))
    .join('\n');
  const mentions = [];
  for (const tool of toolManifest.tools) {
    const matchedAliases = tool.aliases.filter((alias) => corpus.includes(alias));
    if (matchedAliases.length === 0) errors.push(`[${tool.id}] canonical Japanese reader source に alias がありません`);
    mentions.push({ id: tool.id, aliases: matchedAliases, lane: tool.lane });
  }

  for (const [locale, relativePath] of Object.entries(SOURCE_FILES)) {
    const absolutePath = path.join(rootDir, relativePath);
    const content = fs.readFileSync(absolutePath, 'utf8');
    const expected = renderInventory(toolManifest, locale);
    let actual;
    try {
      actual = replaceInventory(content, expected, relativePath);
    } catch (error) {
      errors.push(error.message);
      continue;
    }
    if (actual !== content) errors.push(`${relativePath}: generated tool inventory table が tool manifest と一致しません`);
  }

  const executableVersions = toolManifest.tools
    .filter((tool) => tool.version)
    .map((tool) => ({ id: tool.id, version: tool.version }));
  const duplicateVersionPaths = [
    'tools/bootstrap.sh',
    'tools/alloy-check.sh',
    'tools/tlc-run.sh',
    'tools/apalache-check.sh',
    'tools/dafny-verify.sh',
    'tools/spin-check.sh',
    'tools/nusmv-check.sh',
    'tools/cbmc-check.sh',
    'tools/quint-check.sh',
    'tools/prism-check.sh',
    'tools/tamarin-check.sh',
    'tools/kani-check.sh',
    'tools/rtlola-check.sh',
    '.github/workflows/formal-checks.yml',
    'examples/example-manifest.json',
  ];
  for (const file of duplicateVersionPaths) {
    const content = fs.readFileSync(path.join(rootDir, file), 'utf8');
    for (const tool of executableVersions) {
      if (content.includes(tool.version)) errors.push(`${file}: ${tool.id} version ${tool.version} を重複記載せず tool manifest から参照してください`);
    }
  }

  if (options.writeReport !== false) {
    const reportPath = path.join(rootDir, '.artifacts', 'tool-inventory', 'report.json');
    fs.mkdirSync(path.dirname(reportPath), { recursive: true });
    fs.writeFileSync(reportPath, `${JSON.stringify({
      schemaVersion: 1,
      tools: toolManifest.tools.length,
      laneCounts: Object.fromEntries(
        [...new Set(toolManifest.tools.map((tool) => tool.lane))].sort()
          .map((lane) => [lane, toolManifest.tools.filter((tool) => tool.lane === lane).length]),
      ),
      executableExamples: exampleManifest.examples.length,
      canonicalJapaneseReaderFiles: readers,
      mentions,
      errors,
    }, null, 2)}\n`);
  }
  return errors;
}

function writeInventories(rootDir) {
  const { manifest } = loadToolManifest(rootDir);
  for (const [locale, relativePath] of Object.entries(SOURCE_FILES)) {
    const absolutePath = path.join(rootDir, relativePath);
    const content = fs.readFileSync(absolutePath, 'utf8');
    fs.writeFileSync(absolutePath, replaceInventory(content, renderInventory(manifest, locale), relativePath));
  }
}

function runSelfTest() {
  const manifest = {
    tools: [{
      name: 'Tool | One',
      lane: 'documentation-only',
      version: null,
      reason: { ja: '理由', en: 'Reason' },
    }],
  };
  const rendered = renderInventory(manifest, 'ja');
  if (!rendered.includes('Tool \\| One') || !rendered.includes('documentation-only')) {
    throw new Error('inventory rendering did not escape cells or include the lane');
  }
  const fixture = `before\n${START}\nold\n${END}\nafter\n`;
  const replaced = replaceInventory(fixture, rendered, 'fixture.md');
  if (!replaced.includes('Tool \\| One') || !replaced.endsWith('after\n')) throw new Error('inventory replacement failed');
  console.log('OK: tool inventory renderer self-tests passed.');
}

function main() {
  const args = process.argv.slice(2);
  if (args.length === 1 && args[0] === '--self-test') return runSelfTest();
  if (args.length === 1 && args[0] === '--write') {
    writeInventories(REPO_ROOT);
    console.log('Updated JA/EN tool inventory tables from tools/tool-manifest.json.');
    return;
  }
  if (args.length !== 0) {
    console.error('Usage: node scripts/check-tool-inventory.js [--self-test|--write]');
    process.exitCode = 2;
    return;
  }
  const errors = validateInventory(REPO_ROOT);
  if (errors.length === 0) {
    console.log('OK: tool inventory, versions, examples, reader mentions, and generated tables match.');
    return;
  }
  for (const error of errors) console.error(error);
  process.exitCode = 1;
}

if (require.main === module) main();

module.exports = {
  canonicalJapaneseReaderFiles,
  renderInventory,
  replaceInventory,
  validateInventory,
};
