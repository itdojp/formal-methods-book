#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const yaml = require('yaml');
const { loadPublicationModel } = require('./lib/publication-metadata');
const {
  evaluateTranslationStatus,
  loadTranslationManifest,
  renderTranslationNotice,
} = require('./lib/translation-status');

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

function parseFrontMatter(content, relativePath) {
  const match = content.match(/^---\r?\n([\s\S]*?)\r?\n---\r?\n/);
  if (!match) throw new Error(`${relativePath}: YAML front matter is required`);
  return yaml.parse(match[1]) || {};
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
  const warnings = [];

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
      checkFileExists(publicPath, errors, 'docs must contain a generated page for source file');
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

  let translationReport = {
    schema_version: '1.0',
    evaluation_date: new Date().toISOString().slice(0, 10),
    result: 'error',
    summary: {},
    errors: [],
    warnings: [],
    pages: [],
  };
  try {
    const publicationModel = loadPublicationModel(repoRoot);
    const translationManifest = loadTranslationManifest(repoRoot, publicationModel);
    const evaluation = evaluateTranslationStatus({
      repoRoot,
      publicationModel,
      manifest: translationManifest,
    });

    for (const [relativePath, entry] of Object.entries(translationManifest.pages)) {
      const publicPath = sourceToPublicPath('en', relativePath);
      if (!publicPath || !fs.existsSync(path.join(repoRoot, publicPath))) continue;
      try {
        const publicContent = readFile(publicPath);
        const metadata = parseFrontMatter(publicContent, publicPath);
        const expectedMetadata = {
          translation_status: entry.status,
          translation_source_commit: entry.source_commit,
          translation_reviewed_at: entry.reviewed_at,
          translation_tracking_issue: entry.tracking_issue,
        };
        for (const [key, expected] of Object.entries(expectedMetadata)) {
          if (metadata[key] !== expected) {
            evaluation.errors.push(
              `${relativePath}: public ${key} must be ${JSON.stringify(expected)}, found ${JSON.stringify(metadata[key])}`,
            );
          }
        }
        const expectedNotice = renderTranslationNotice(entry);
        if (!publicContent.includes(expectedNotice)) {
          evaluation.errors.push(`${relativePath}: public translation status notice is missing or stale`);
        }
      } catch (error) {
        evaluation.errors.push(`${relativePath}: cannot verify public translation status: ${error.message}`);
      }
    }
    evaluation.summary.errors = evaluation.errors.length;
    errors.push(...evaluation.errors);
    warnings.push(...evaluation.warnings);
    translationReport = {
      schema_version: '1.0',
      evaluation_date: new Date().toISOString().slice(0, 10),
      source_locale: translationManifest.source_locale,
      translation_locale: translationManifest.translation_locale,
      policy: translationManifest.policy,
      result: evaluation.errors.length === 0 ? 'pass' : 'error',
      summary: evaluation.summary,
      errors: evaluation.errors,
      warnings: evaluation.warnings,
      pages: evaluation.pages,
    };
  } catch (error) {
    const message = `translation status evaluation failed: ${error.message}`;
    errors.push(message);
    translationReport.errors.push(message);
  }

  const reportPath = path.join(repoRoot, '.artifacts', 'translation-status', 'report.json');
  fs.mkdirSync(path.dirname(reportPath), { recursive: true });
  fs.writeFileSync(reportPath, `${JSON.stringify(translationReport, null, 2)}\n`);

  if (process.argv.includes('--inventory')) {
    for (const page of translationReport.pages) {
      const mismatch = page.mismatches.length > 0 ? page.mismatches.join(',') : '-';
      console.log(`${page.status.padEnd(7)} ${page.relative_path} mismatches=${mismatch}`);
      if (page.mismatches.includes('heading_structure') || page.mismatches.includes('numbered_heading_ids')) {
        console.log(`         ja.heading_levels=${page.source_features.heading_levels.join(',') || '-'}`);
        console.log(`         en.heading_levels=${page.translation_features.heading_levels.join(',') || '-'}`);
        console.log(`         ja.numbered_ids=${page.source_features.numbered_heading_ids.join(',') || '-'}`);
        console.log(`         en.numbered_ids=${page.translation_features.numbered_heading_ids.join(',') || '-'}`);
      }
    }
  }

  if (warnings.length > 0) {
    console.warn(`Bilingual integrity warnings (${warnings.length}):`);
    for (const warning of warnings) console.warn(`- ${warning}`);
  }

  if (errors.length > 0) {
    console.error('Bilingual integrity check failed:');
    for (const error of errors) {
      console.error(`- ${error}`);
    }
    process.exit(1);
  }

  const counts = translationReport.summary?.status_counts || {};
  console.log(
    `Bilingual integrity check passed (${translationReport.summary?.total_pages || 0} tracked pages: `
      + `synced=${counts.synced || 0}, partial=${counts.partial || 0}, stale=${counts.stale || 0}).`,
  );
  console.log(`Translation status report: ${path.relative(repoRoot, reportPath)}`);
}

main();
