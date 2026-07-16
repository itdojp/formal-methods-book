#!/usr/bin/env node
/*
  Bilingual builder.
  - JA publish root stays at docs/
  - EN publish root stays at docs/en/
  - Publication metadata is generated from edition configs before content
  - JA chapters remain hand-maintained under docs/chapters/
  - EN public pages are generated from src/en/** skeletons
*/
const fs = require('fs');
const path = require('path');
const {
  loadPublicationModel,
  renderGeneratedArtifacts,
  resolveSourcePage,
  writeGeneratedArtifacts,
} = require('./lib/publication-metadata');

const repoRoot = path.resolve(__dirname, '..');
const manifestPath = path.join(repoRoot, 'book-config.json');
const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
const editions = manifest.editions || {};
const target = process.argv[2] || 'all';
const validTargets = new Set(['ja', 'en', 'all']);

if (!validTargets.has(target)) {
  console.error(`Unsupported build target: ${target}`);
  console.error('Usage: node scripts/build.js [ja|en|all]');
  process.exit(1);
}

function ensureDir(dirPath) {
  fs.mkdirSync(dirPath, { recursive: true });
}

function cleanDir(dirPath) {
  if (!fs.existsSync(dirPath)) return;
  for (const entry of fs.readdirSync(dirPath)) {
    fs.rmSync(path.join(dirPath, entry), { recursive: true, force: true });
  }
}

function escapeYaml(value) {
  return String(value || '').replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

function readMarkdownTitle(content, fallback) {
  const match = content.match(/^#\s+(.+)$/m);
  if (match) return match[1].trim();
  return fallback;
}

function stripEnglishTranslationMetadata(content) {
  return content.replace(
    /(^# [^\r\n]+\r?\n\r?\n)> Translation status:[^\r\n]*\r?\n> Japanese source of truth:[^\r\n]*\r?\n\r?\n/,
    '$1'
  );
}

function rewriteExampleLinksForPublication(content) {
  const revision = "{{site.github.build_revision|default:'main'}}";
  return content.replace(
    /\[(examples\/[A-Za-z0-9_./-]+)\]\([^)]+\)/g,
    (_, repositoryPath) =>
      `[${repositoryPath}](https://github.com/itdojp/formal-methods-book/blob/${revision}/${repositoryPath})`,
  );
}

function wrapWithFrontMatter({ title, description, locale, sourcePath }, content) {
  const lines = [
    '---',
    'layout: book',
    `title: "${escapeYaml(title)}"`,
    ...(description ? [`description: "${escapeYaml(description)}"`] : []),
    `locale: "${locale}"`,
    `lang: "${locale}"`,
    `source_path: "${sourcePath}"`,
    '---',
    ''
  ];
  return `${lines.join('\n')}${content.trimEnd()}\n`;
}

function shouldBuildFile(locale, relativePath) {
  const posixPath = relativePath.split(path.sep).join('/');
  if (posixPath === 'appendices/appendices_draft.md') return false;
  if (locale === 'ja' && /^chapters\//.test(posixPath)) return false;
  return true;
}

function collectSourceFiles(sourceRoot) {
  const files = [];
  function walk(dirPath) {
    for (const entry of fs.readdirSync(dirPath, { withFileTypes: true })) {
      const absolutePath = path.join(dirPath, entry.name);
      if (entry.isDirectory()) {
        walk(absolutePath);
        continue;
      }
      if (entry.isFile() && entry.name.endsWith('.md')) {
        files.push(absolutePath);
      }
    }
  }
  walk(sourceRoot);
  return files.sort();
}

function buildEdition(locale) {
  const edition = editions[locale];
  if (!edition) {
    throw new Error(`Edition config not found: ${locale}`);
  }

  const sourceRoot = path.join(repoRoot, edition.sourceRoot);
  const publishRoot = path.join(repoRoot, edition.publishRoot);
  if (!fs.existsSync(sourceRoot)) {
    throw new Error(`Source root not found: ${edition.sourceRoot}`);
  }

  if (locale === 'en') {
    ensureDir(publishRoot);
    cleanDir(publishRoot);
  } else {
    ensureDir(path.join(publishRoot, 'appendices'));
    cleanDir(path.join(publishRoot, 'appendices'));
  }

  const sourceFiles = collectSourceFiles(sourceRoot);
  for (const sourceFile of sourceFiles) {
    const relativePath = path.relative(sourceRoot, sourceFile);
    if (!shouldBuildFile(locale, relativePath)) continue;

    const page = resolveSourcePage(publicationModel.editions[locale], relativePath);
    if (!page) continue;
    const outputFile = path.join(publishRoot, ...page.outputSegments);

    let content = fs.readFileSync(sourceFile, 'utf8');
    if (locale === 'en') {
      content = stripEnglishTranslationMetadata(content);
    }
    content = rewriteExampleLinksForPublication(content);
    const canonicalMetadata = page.metadata;
    const title = canonicalMetadata?.title || readMarkdownTitle(content, path.basename(relativePath, '.md'));
    const wrapped = wrapWithFrontMatter({
      title,
      description: canonicalMetadata?.description,
      locale,
      sourcePath: path.join(edition.sourceRoot, relativePath).split(path.sep).join('/'),
    }, content);

    ensureDir(path.dirname(outputFile));
    fs.writeFileSync(outputFile, wrapped);
  }

  console.log(`Built ${locale} edition into ${edition.publishRoot}.`);
}

const publicationModel = loadPublicationModel(repoRoot);
writeGeneratedArtifacts(repoRoot, renderGeneratedArtifacts(publicationModel));

if (target === 'all') {
  buildEdition('ja');
  buildEdition('en');
} else {
  buildEdition(target);
}
