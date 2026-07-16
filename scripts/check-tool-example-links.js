#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const {
  MANIFEST_PATH,
  expectedReferences,
  loadManifest,
  runnerCommand,
  validateManifest,
} = require('./example-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');
const REPOSITORY_BLOB_BASE = 'https://github.com/itdojp/formal-methods-book/blob/';
const BUILD_REVISION_TEMPLATE = "{{site.github.build_revision|default:'main'}}";

function reportError(error) {
  const safeMessage = String(error.message).replace(/\r?\n/g, ' ');
  console.error(`::error file=${error.filePath},line=${error.line || 1}::${safeMessage}`);
}

function repositoryLink(repositoryPath, reference) {
  if (reference.startsWith('src/')) {
    const relativePath = path.posix.relative(path.posix.dirname(reference), repositoryPath);
    return `[${repositoryPath}](${relativePath})`;
  }
  return `[${repositoryPath}](${REPOSITORY_BLOB_BASE}${BUILD_REVISION_TEMPLATE}/${repositoryPath})`;
}

function findAnchorLine(lines, anchor) {
  const escaped = anchor.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const patterns = [
    new RegExp(`<a\\s+(?:[^>]*\\s)?id=["']${escaped}["'][^>]*>`, 'i'),
    new RegExp(`\\{:\\s*#${escaped}(?:\\s|\\})`),
    new RegExp(`\\{#${escaped}(?:\\s|\\})`),
  ];
  return lines.findIndex((line) => patterns.some((pattern) => pattern.test(line)));
}

function sectionForAnchor(content, anchor) {
  const lines = content.split(/\r?\n/);
  const anchorLine = findAnchorLine(lines, anchor);
  if (anchorLine < 0) return null;

  let headingLine = anchorLine;
  while (headingLine < lines.length && !/^#{1,6}\s/.test(lines[headingLine])) headingLine += 1;
  if (headingLine >= lines.length) headingLine = anchorLine;
  const headingMatch = lines[headingLine].match(/^(#{1,6})\s/);
  const level = headingMatch ? headingMatch[1].length : 6;
  let end = headingLine + 1;
  while (end < lines.length) {
    const match = lines[end].match(/^(#{1,6})\s/);
    if (match && match[1].length <= level) break;
    end += 1;
  }
  return { lines: lines.slice(anchorLine, end), anchorLine: anchorLine + 1 };
}

function collectMarkdownFiles(rootDir) {
  const files = [];
  function walk(relativeDir) {
    const absoluteDir = path.join(rootDir, relativeDir);
    if (!fs.existsSync(absoluteDir)) return;
    for (const entry of fs.readdirSync(absoluteDir, { withFileTypes: true })) {
      if (entry.isDirectory() && ['_site', 'node_modules', '.git'].includes(entry.name)) continue;
      const relativePath = path.posix.join(relativeDir.split(path.sep).join('/'), entry.name);
      if (entry.isDirectory()) walk(relativePath);
      else if (entry.isFile() && entry.name.endsWith('.md')) files.push(relativePath);
    }
  }
  walk('src');
  walk('docs');
  return files.sort();
}

function validateRepository(rootDir, manifestOverride = null) {
  let manifest;
  let manifestPath = MANIFEST_PATH;
  const errors = [];
  try {
    if (manifestOverride) {
      manifest = manifestOverride;
    } else {
      ({ manifest, manifestPath } = loadManifest(rootDir));
    }
  } catch (error) {
    return [{ filePath: manifestPath, line: 1, message: error.message }];
  }

  errors.push(...validateManifest(manifest, { rootDir, manifestPath }));
  if (!manifest || !Array.isArray(manifest.examples)) return errors;

  const entryById = new Map(
    manifest.examples
      .filter((entry) => entry && typeof entry.id === 'string')
      .map((entry) => [entry.id, entry]),
  );
  const registrationPattern = /<!-- example-contract: ([a-z0-9]+(?:-[a-z0-9]+)*) -->/g;
  for (const reference of collectMarkdownFiles(rootDir)) {
    const content = fs.readFileSync(path.join(rootDir, reference), 'utf8');
    for (const match of content.matchAll(registrationPattern)) {
      const entry = entryById.get(match[1]);
      if (!entry) continue; // check-tool-blocks.js reports unknown registrations.
      if (!Array.isArray(entry.references) || !entry.references.includes(reference)) {
        errors.push({
          filePath: reference,
          line: content.slice(0, match.index).split(/\r?\n/).length,
          message: `[${entry.id}] contract registration file が manifest references にありません`,
        });
      }
    }
  }

  for (const entry of manifest.examples) {
    if (!entry || typeof entry !== 'object') continue;
    const actualReferences = new Set(Array.isArray(entry.references) ? entry.references : []);
    const requiredReferences = expectedReferences(entry.chapter);
    for (const reference of requiredReferences) {
      if (!actualReferences.has(reference)) {
        errors.push({
          filePath: manifestPath,
          line: 1,
          message: `[${entry.id}] JA/EN source/public reference が不足しています: ${reference}`,
        });
      }
    }
    if (!Array.isArray(entry.references)) continue;

    for (const reference of entry.references) {
      const absolutePath = path.join(rootDir, reference);
      if (!fs.existsSync(absolutePath)) continue;
      const content = fs.readFileSync(absolutePath, 'utf8');
      const section = sectionForAnchor(content, entry.anchor);
      if (!section) {
        errors.push({
          filePath: reference,
          line: 1,
          message: `[${entry.id}] anchor が存在しません: ${entry.anchor}`,
        });
        continue;
      }
      const sectionContent = section.lines.join('\n');
      const registration = `<!-- example-contract: ${entry.id} -->`;
      if (!sectionContent.includes(registration)) {
        errors.push({
          filePath: reference,
          line: section.anchorLine,
          message: `[${entry.id}] anchor section に contract registration がありません: ${registration}`,
        });
      }
      const command = runnerCommand(entry.id);
      if (!section.lines.some((line) => line.trim() === command)) {
        errors.push({
          filePath: reference,
          line: section.anchorLine,
          message: `[${entry.id}] anchor section に正規 runner command がありません: ${command}`,
        });
      }
      for (const asset of entry.assets || []) {
        const link = repositoryLink(asset, reference);
        if (!sectionContent.includes(link)) {
          errors.push({
            filePath: reference,
            line: section.anchorLine,
            message: `[${entry.id}] anchor section に clickable asset link がありません: ${link}`,
          });
        }
      }
      if (entry.config && !sectionContent.includes(repositoryLink(entry.config, reference))) {
        errors.push({
          filePath: reference,
          line: section.anchorLine,
          message: `[${entry.id}] anchor section に clickable config link がありません: ${repositoryLink(entry.config, reference)}`,
        });
      }
    }
  }
  return errors;
}

function writeFixture(rootDir, mutate = null, documentId = 'chapter04') {
  const id = 'alloy-valid';
  const anchor = documentId.startsWith('appendix-')
    ? 'appendix-executable-example-contracts'
    : 'executable-example-contracts';
  const entry = {
    id,
    tool: 'alloy',
    version: '6.2.0',
    chapter: documentId,
    anchor,
    references: expectedReferences(documentId),
    assets: ['examples/alloy/valid.als'],
    config: null,
    command: 'bash tools/alloy-check.sh examples/alloy/valid.als',
    lane: 'pr-quick',
    expected: { exitCode: 0, stdoutMarker: 'SAT' },
  };
  const manifest = { schemaVersion: 1, examples: [entry] };
  if (mutate) mutate({ manifest, entry, rootDir });

  fs.mkdirSync(path.join(rootDir, 'examples/alloy'), { recursive: true });
  fs.mkdirSync(path.join(rootDir, 'tools'), { recursive: true });
  fs.writeFileSync(path.join(rootDir, 'examples/alloy/valid.als'), 'run {}\n');
  fs.writeFileSync(path.join(rootDir, 'tools/alloy-check.sh'), '#!/usr/bin/env bash\n');
  for (const reference of entry.references) {
    const absolutePath = path.join(rootDir, reference);
    fs.mkdirSync(path.dirname(absolutePath), { recursive: true });
    fs.writeFileSync(
      absolutePath,
      [
        '# Chapter',
        '',
        `## Contracts {: #${anchor} }`,
        '',
        repositoryLink('examples/alloy/valid.als', reference),
        '',
        `<!-- example-contract: ${id} -->`,
        '【Tool-compliant (runs as-is)】',
        '```bash',
        runnerCommand(id),
        '```',
        '',
      ].join('\n'),
    );
  }
  return manifest;
}

function runSelfTest() {
  const parent = path.join(REPO_ROOT, 'tools', '.tmp');
  fs.mkdirSync(parent, { recursive: true });
  const selfTestRoot = fs.mkdtempSync(path.join(parent, 'example-link-self-test-'));
  const tests = [
    {
      name: 'valid manifest',
      prepare: null,
      expected: null,
    },
    {
      name: 'valid appendix manifest',
      prepare: null,
      expected: null,
      documentId: 'appendix-a',
    },
    {
      name: 'missing asset',
      prepare: ({ rootDir }) => fs.rmSync(path.join(rootDir, 'examples/alloy/valid.als')),
      expected: 'asset file が存在しません',
    },
    {
      name: 'missing bilingual reference',
      prepare: ({ entry }) => { entry.references.pop(); },
      expected: 'JA/EN source/public reference が不足しています',
    },
    {
      name: 'broken asset link',
      prepare: ({ entry, rootDir }) => {
        const reference = path.join(rootDir, entry.references[0]);
        const content = fs.readFileSync(reference, 'utf8');
        fs.writeFileSync(
          reference,
          content.replace(repositoryLink(entry.assets[0], entry.references[0]), '`broken link`'),
        );
      },
      expected: 'clickable asset link がありません',
    },
    {
      name: 'registration outside manifest references',
      prepare: ({ rootDir }) => {
        const extra = path.join(rootDir, 'src', 'ja', 'chapters', 'chapter02.md');
        fs.mkdirSync(path.dirname(extra), { recursive: true });
        fs.writeFileSync(extra, '<!-- example-contract: alloy-valid -->\n');
      },
      expected: 'contract registration file が manifest references にありません',
    },
    {
      name: 'duplicate ID',
      prepare: ({ manifest }) => manifest.examples.push({ ...manifest.examples[0] }),
      expected: 'id が重複しています',
    },
    {
      name: 'broken anchor',
      prepare: ({ entry }) => { entry.anchor = 'broken-anchor'; },
      expected: 'anchor が存在しません',
    },
    {
      name: 'broken command',
      prepare: ({ entry }) => { entry.command = 'echo broken'; },
      expected: 'command は bash tools/alloy-check.sh と asset 引数で開始する必要があります',
    },
    {
      name: 'path traversal command',
      prepare: ({ entry }) => {
        entry.command = 'bash tools/alloy-check.sh --out-dir ../../tools/.cache examples/alloy/valid.als';
      },
      expected: 'command token が許可されていません',
    },
    {
      name: 'unapproved tool option',
      prepare: ({ entry }) => {
        entry.command = 'bash tools/alloy-check.sh --unknown value examples/alloy/valid.als';
      },
      expected: '許可されていない option',
    },
    {
      name: 'excessive numeric option',
      prepare: ({ entry }) => {
        entry.command = 'bash tools/alloy-check.sh --repeat 1000000 examples/alloy/valid.als';
      },
      expected: '--repeat は 100 以下',
    },
  ];

  try {
    for (let index = 0; index < tests.length; index += 1) {
      const test = tests[index];
      const rootDir = path.join(selfTestRoot, String(index));
      const manifest = writeFixture(rootDir, null, test.documentId || 'chapter04');
      if (test.prepare) test.prepare({ manifest, entry: manifest.examples[0], rootDir });
      const errors = validateRepository(rootDir, manifest);
      if (test.expected === null && errors.length !== 0) {
        throw new Error(`${test.name}: unexpected errors: ${errors.map((e) => e.message).join(' | ')}`);
      }
      if (test.expected !== null && !errors.some((error) => error.message.includes(test.expected))) {
        throw new Error(`${test.name}: expected diagnostic not found: ${test.expected}`);
      }
      console.log(`PASS: ${test.name}`);
    }
  } finally {
    fs.rmSync(selfTestRoot, { recursive: true, force: true });
  }
  console.log('OK: tool example link self-tests passed.');
}

function main() {
  if (process.argv.includes('--self-test')) {
    runSelfTest();
    return;
  }
  if (process.argv.length > 2) {
    console.error('Usage: node scripts/check-tool-example-links.js [--self-test]');
    process.exitCode = 2;
    return;
  }

  const errors = validateRepository(REPO_ROOT);
  if (errors.length === 0) {
    console.log('OK: example manifest schema, paths, references, anchors, assets, and commands are valid.');
    return;
  }
  for (const error of errors) reportError(error);
  console.error(`Found ${errors.length} example manifest/link error(s).`);
  process.exitCode = 1;
}

main();

module.exports = { validateRepository };
