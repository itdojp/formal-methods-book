#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const yaml = require('yaml');

const repoRoot = path.resolve(__dirname, '..');
const japanesePattern = /[\p{Script=Hiragana}\p{Script=Katakana}\p{Script=Han}]/u;
const allowedJapaneseLines = new Set([
  '【ツール準拠（そのまま動く）】',
  '【文脈依存スニペット】',
  '【擬似記法】',
]);
const sourceSections = [
  'index.md',
  'glossary/index.md',
  'introduction/index.md',
  'afterword/index.md',
];

function readFile(relativePath) {
  return fs.readFileSync(path.join(repoRoot, relativePath), 'utf8');
}

function readJson(relativePath) {
  return JSON.parse(readFile(relativePath));
}

function readYaml(relativePath) {
  return yaml.parse(readFile(relativePath));
}

function collectMarkdownFiles(dir, matcher) {
  const targetDir = path.join(repoRoot, dir);
  if (!fs.existsSync(targetDir)) {
    return [];
  }
  return fs
    .readdirSync(targetDir)
    .filter((name) => matcher.test(name))
    .sort()
    .map((name) => path.posix.join(dir, name));
}

function flattenNavigation(navigation) {
  const sections = ['introduction', 'chapters', 'additional', 'resources', 'appendices', 'afterword'];
  const items = [];
  for (const section of sections) {
    for (const item of navigation?.[section] || []) {
      items.push(item);
    }
  }
  return items;
}

function expectedEnglishPath(japanesePath) {
  if (japanesePath === '/') {
    return '/en/';
  }
  return `/en${japanesePath}`;
}

function sourceToPublicPath(locale, relativeSourcePath) {
  if (relativeSourcePath === 'index.md') {
    return locale === 'ja' ? 'docs/index.md' : 'docs/en/index.md';
  }
  if (relativeSourcePath === 'glossary/index.md') {
    return locale === 'ja' ? 'docs/glossary/index.md' : 'docs/en/glossary/index.md';
  }
  if (relativeSourcePath === 'introduction/index.md') {
    return locale === 'ja' ? 'docs/introduction/index.md' : 'docs/en/introduction/index.md';
  }
  if (relativeSourcePath === 'afterword/index.md') {
    return locale === 'ja' ? 'docs/afterword/index.md' : 'docs/en/afterword/index.md';
  }
  if (relativeSourcePath.startsWith('chapters/')) {
    const slug = path.posix.basename(relativeSourcePath, '.md');
    return locale === 'ja'
      ? `docs/chapters/${slug}/index.md`
      : `docs/en/chapters/${slug}/index.md`;
  }
  if (relativeSourcePath.startsWith('appendices/')) {
    const slug = path.posix.basename(relativeSourcePath, '.md');
    return locale === 'ja'
      ? `docs/appendices/${slug}/index.md`
      : `docs/en/appendices/${slug}/index.md`;
  }
  return null;
}

function checkFileExists(relativePath, errors, message) {
  const absolutePath = path.join(repoRoot, relativePath);
  if (!fs.existsSync(absolutePath)) {
    errors.push(`${message}: ${relativePath}`);
  }
}

function collectSourceInventory(locale) {
  const files = [...sourceSections];
  for (const filePath of collectMarkdownFiles(`src/${locale}/chapters`, /^chapter\d+\.md$/)) {
    files.push(filePath.replace(`src/${locale}/`, ''));
  }
  for (const filePath of collectMarkdownFiles(`src/${locale}/appendices`, /^appendix-.*\.md$/)) {
    files.push(filePath.replace(`src/${locale}/`, ''));
  }
  return files.sort();
}

function main() {
  const errors = [];

  const manifest = readJson('book-config.json');
  const jaConfig = readJson('book-config.ja.json');
  const enConfig = readJson('book-config.en.json');
  const navigation = readYaml('docs/_data/navigation.yml');
  const locales = readYaml('docs/_data/locales.yml');

  if (manifest.project?.defaultEdition !== 'ja') {
    errors.push('book-config.json: defaultEdition must remain "ja".');
  }
  if (manifest.editions?.ja?.sourceRoot !== 'src/ja' || manifest.editions?.en?.sourceRoot !== 'src/en') {
    errors.push('book-config.json: edition sourceRoot values must be src/ja and src/en.');
  }
  if (manifest.editions?.ja?.publishRoot !== 'docs' || manifest.editions?.en?.publishRoot !== 'docs/en') {
    errors.push('book-config.json: edition publishRoot values must be docs and docs/en.');
  }

  const jaChapterIds = (jaConfig.structure?.chapters || []).map((item) => item.id);
  const enChapterIds = (enConfig.structure?.chapters || []).map((item) => item.id);
  if (JSON.stringify(jaChapterIds) !== JSON.stringify(enChapterIds)) {
    errors.push('book-config.ja.json / book-config.en.json: chapter IDs must match 1:1.');
  }
  const jaAppendixIds = (jaConfig.structure?.appendices || []).map((item) => item.id);
  const enAppendixIds = (enConfig.structure?.appendices || []).map((item) => item.id);
  if (JSON.stringify(jaAppendixIds) !== JSON.stringify(enAppendixIds)) {
    errors.push('book-config.ja.json / book-config.en.json: appendix IDs must match 1:1.');
  }

  if (!navigation?.ja || !navigation?.en) {
    errors.push('docs/_data/navigation.yml: both ja and en navigation trees are required.');
  } else {
    const jaNavItems = flattenNavigation(navigation.ja);
    const enNavItems = flattenNavigation(navigation.en);
    if (jaNavItems.length !== enNavItems.length) {
      errors.push('docs/_data/navigation.yml: ja/en navigation item counts must match.');
    }

    const compareCount = Math.min(jaNavItems.length, enNavItems.length);
    for (let index = 0; index < compareCount; index += 1) {
      const jaItem = jaNavItems[index];
      const enItem = enNavItems[index];
      const expectedPath = expectedEnglishPath(jaItem.path);
      if (enItem.path !== expectedPath) {
        errors.push(
          `docs/_data/navigation.yml: expected EN path ${expectedPath} for JA path ${jaItem.path}, found ${enItem.path}.`,
        );
      }
    }
  }

  if (!locales?.ja || !locales?.en) {
    errors.push('docs/_data/locales.yml: both ja and en locale definitions are required.');
  }

  const jaInventory = collectSourceInventory('ja');
  const enInventory = collectSourceInventory('en');
  if (JSON.stringify(jaInventory) !== JSON.stringify(enInventory)) {
    const missingInEn = jaInventory.filter((item) => !enInventory.includes(item));
    const missingInJa = enInventory.filter((item) => !jaInventory.includes(item));
    if (missingInEn.length > 0) {
      errors.push(`src/en: missing counterparts for ${missingInEn.join(', ')}`);
    }
    if (missingInJa.length > 0) {
      errors.push(`src/ja: missing counterparts for ${missingInJa.join(', ')}`);
    }
  }

  for (const relativeSourcePath of enInventory) {
    checkFileExists(
      sourceToPublicPath('en', relativeSourcePath),
      errors,
      'docs/en must contain a generated page for source file',
    );
  }
  for (const relativeSourcePath of jaInventory) {
    const publicPath = sourceToPublicPath('ja', relativeSourcePath);
    if (publicPath) {
      checkFileExists(publicPath, errors, 'docs must contain a generated or maintained page for source file');
    }
  }

  checkFileExists('docs/index.md', errors, 'docs root page is required');
  checkFileExists('docs/en/index.md', errors, 'docs/en root page is required');

  function walkEnglishDocs(dir) {
    const entries = fs.readdirSync(path.join(repoRoot, dir), { withFileTypes: true });
    for (const entry of entries) {
      const relative = path.posix.join(dir, entry.name);
      if (entry.isDirectory()) {
        walkEnglishDocs(relative);
        continue;
      }
      if (!entry.name.endsWith('.md')) {
        continue;
      }
      const content = readFile(relative);
      const lines = content.split('\n');
      for (let index = 0; index < lines.length; index += 1) {
        const line = lines[index];
        if (line.includes('bilingual-qa:allow-ja')) {
          continue;
        }
        if (allowedJapaneseLines.has(line.trim())) {
          continue;
        }
        if (japanesePattern.test(line)) {
          errors.push(`${relative}:${index + 1}: obvious Japanese leakage detected in docs/en output.`);
          break;
        }
      }
    }
  }

  if (fs.existsSync(path.join(repoRoot, 'docs', 'en'))) {
    walkEnglishDocs('docs/en');
  }

  if (errors.length > 0) {
    console.error('Bilingual integrity check failed:');
    for (const error of errors) {
      console.error(`- ${error}`);
    }
    process.exit(1);
  }

  console.log('Bilingual integrity check passed.');
}

main();
