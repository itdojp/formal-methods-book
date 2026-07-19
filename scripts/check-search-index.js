#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { loadPublicationModel } = require('./lib/publication-metadata');
const { renderEditionPages } = require('./lib/publication-build');
const {
  SEARCH_INDEX_MAX_ENTRIES,
  SEARCH_INDEX_MAX_BYTES,
  pageDescriptors,
  renderSearchIndex,
  searchIndexOutputPath,
  serializeSearchIndex,
} = require('./lib/search-index');

const repoRoot = path.resolve(__dirname, '..');
const model = loadPublicationModel(repoRoot);

function fail(errors) {
  if (errors.length === 0) return;
  console.error(`Search index check failed (${errors.length}):`);
  for (const error of errors) console.error(`- ${error}`);
  process.exit(1);
}

function readIndex(filePath, errors) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    errors.push(`${path.relative(repoRoot, filePath)}: ${error.message}`);
    return null;
  }
}

function validateIndex(index, locale, expectedPages, errors) {
  if (!index) return;
  if (index.schemaVersion !== 1) errors.push(`${locale}: schemaVersion must be 1`);
  if (index.project !== model.manifest.project.id) errors.push(`${locale}: project mismatch`);
  if (index.projectVersion !== model.manifest.project.version) errors.push(`${locale}: projectVersion mismatch`);
  if (index.locale !== locale) errors.push(`${locale}: locale mismatch`);
  if (!Array.isArray(index.entries)) {
    errors.push(`${locale}: entries must be an array`);
    return;
  }
  if (index.entryCount !== index.entries.length) errors.push(`${locale}: entryCount mismatch`);
  if (index.entries.length > SEARCH_INDEX_MAX_ENTRIES) {
    errors.push(`${locale}: ${index.entries.length} entries exceed the ${SEARCH_INDEX_MAX_ENTRIES} browser limit`);
  }

  const ids = new Set();
  const urls = new Set();
  const indexedPages = new Set();
  for (const [position, entry] of index.entries.entries()) {
    const label = `${locale} entries[${position}]`;
    for (const field of ['id', 'locale', 'pageId', 'section', 'title', 'chapter', 'heading', 'url', 'text']) {
      if (typeof entry?.[field] !== 'string' || !entry[field].trim()) errors.push(`${label}.${field}: non-empty string required`);
    }
    if (!Array.isArray(entry?.aliases) || entry.aliases.some((alias) => typeof alias !== 'string' || !alias.trim())) {
      errors.push(`${label}.aliases: string array required`);
    }
    if (entry.locale !== locale) errors.push(`${label}.locale mismatch`);
    if (!entry.url.startsWith(`/${model.manifest.project.id}/`)) errors.push(`${label}.url: project base path required`);
    if (ids.has(entry.id)) errors.push(`${label}.id: duplicate ${entry.id}`);
    if (urls.has(entry.url)) errors.push(`${label}.url: duplicate ${entry.url}`);
    ids.add(entry.id);
    urls.add(entry.url);
    indexedPages.add(entry.pageId);
  }
  for (const descriptor of expectedPages) {
    if (!indexedPages.has(descriptor.id)) errors.push(`${locale}: missing indexed page ${descriptor.id}`);
  }

  const serialized = Buffer.from(serializeSearchIndex(index));
  if (serialized.byteLength > SEARCH_INDEX_MAX_BYTES) {
    errors.push(`${locale}: ${serialized.byteLength} byte index exceeds ${SEARCH_INDEX_MAX_BYTES} byte budget`);
  }
}

function checkGenerated() {
  const errors = [];
  const indexes = {};
  for (const locale of Object.keys(model.manifest.editions)) {
    const pages = renderEditionPages(repoRoot, model, locale);
    const expected = renderSearchIndex({ repoRoot, model, locale, pages });
    const outputPath = searchIndexOutputPath(model, locale);
    const outputFile = path.join(repoRoot, outputPath);
    const actual = readIndex(outputFile, errors);
    indexes[locale] = actual;
    if (actual && fs.readFileSync(outputFile, 'utf8') !== serializeSearchIndex(expected)) {
      errors.push(`${outputPath}: stale or manually edited generated search index`);
    }
    validateIndex(actual, locale, pageDescriptors(model, locale), errors);
  }

  const ja = indexes.ja?.entries || [];
  const en = indexes.en?.entries || [];
  if (!ja.some((entry) => entry.pageId === 'chapter09' && entry.text.includes('LeanDojo'))) {
    errors.push('ja: Chapter 9 LeanDojo acceptance marker is not searchable');
  }
  if (!ja.some((entry) => entry.pageId === 'chapter09'
      && entry.heading.includes('カーネル受理と残存仮定の確認')
      && entry.text.includes('Print Assumptions implication_transitivity.'))) {
    errors.push('ja: Chapter 9 Rocq assumption-audit marker is not searchable');
  }
  if (!en.some((entry) => entry.pageId === 'chapter09'
      && entry.heading.includes('Checking Kernel Acceptance and Residual Assumptions')
      && entry.text.includes('Print Assumptions implication_transitivity.'))) {
    errors.push('en: Chapter 9 Rocq assumption-audit marker is not searchable');
  }
  if (!ja.some((entry) => entry.pageId === 'chapter07'
      && entry.heading.includes('simulationによるランダム欠陥探索')
      && entry.text.includes('性質の証明ではありません'))) {
    errors.push('ja: Chapter 7 simulation assurance-boundary marker is not searchable');
  }
  if (!en.some((entry) => entry.pageId === 'chapter07'
      && entry.heading.includes('Randomized Defect Search with Simulation')
      && entry.text.includes('does not prove the property'))) {
    errors.push('en: Chapter 7 simulation assurance-boundary marker is not searchable');
  }
  if (!en.some((entry) => entry.pageId === 'chapter08' && /model checking/iu.test(`${entry.heading} ${entry.text}`))) {
    errors.push('en: Chapter 8 model checking acceptance marker is not searchable');
  }
  if (!ja.some((entry) => entry.aliases.includes('TLA Plus'))) errors.push('ja: TLA Plus alias is missing');
  if (!ja.some((entry) => entry.aliases.includes('model checking'))) errors.push('ja: model checking alias is missing');
  if (!en.some((entry) => entry.aliases.includes('Coq'))) errors.push('en: Coq alias is missing');

  const layout = fs.readFileSync(path.join(repoRoot, 'docs/_layouts/book.html'), 'utf8');
  for (const marker of [
    'role="combobox"', 'aria-autocomplete="list"', 'aria-controls="search-results"',
    'aria-activedescendant', 'role="listbox"', 'aria-live="polite"', 'data-index-url=',
  ]) {
    if (!layout.includes(marker) && marker !== 'aria-activedescendant') errors.push(`layout: missing ${marker}`);
  }
  if (!layout.includes('maxlength="128"')) errors.push('layout: search query maxlength must remain 128');
  const browserSource = fs.readFileSync(path.join(repoRoot, 'docs/assets/js/search.js'), 'utf8');
  for (const marker of ['aria-activedescendant', 'ArrowDown', 'ArrowUp', 'Enter', 'Escape', 'fetchFunction']) {
    if (!browserSource.includes(marker)) errors.push(`search.js: missing ${marker}`);
  }
  if (/\.innerHTML\s*=|insertAdjacentHTML/u.test(browserSource)) errors.push('search.js: unsafe HTML-string rendering is forbidden');
  if (!browserSource.includes(`const MAX_INDEX_ENTRIES = ${SEARCH_INDEX_MAX_ENTRIES};`)) {
    errors.push(`search.js: browser entry limit must remain ${SEARCH_INDEX_MAX_ENTRIES}`);
  }
  if (Buffer.byteLength(browserSource) > 64 * 1024) errors.push('search.js: initial-load asset exceeds 64 KiB budget');

  fail(errors);
  for (const [locale, index] of Object.entries(indexes)) {
    const output = path.join(repoRoot, searchIndexOutputPath(model, locale));
    console.log(`${locale}: ${index.entryCount} entries, ${fs.statSync(output).size} bytes`);
  }
  console.log('Generated search indexes are valid and deterministic.');
}

function htmlIds(html) {
  const ids = new Set();
  const pattern = /\bid=(?:"([^"]+)"|'([^']+)')/gu;
  for (const match of html.matchAll(pattern)) ids.add(match[1] || match[2]);
  return ids;
}

function siteFileForUrl(siteRoot, urlValue) {
  const [pathname, fragment = ''] = urlValue.split('#', 2);
  const basePath = `/${model.manifest.project.id}`;
  if (pathname !== basePath && !pathname.startsWith(`${basePath}/`)) return { file: null, fragment };
  const relative = pathname.slice(basePath.length).replace(/^\//u, '');
  return {
    file: relative ? path.join(siteRoot, relative, 'index.html') : path.join(siteRoot, 'index.html'),
    fragment: decodeURIComponent(fragment),
  };
}

function checkSite(siteArgument) {
  const errors = [];
  const siteRoot = path.resolve(repoRoot, siteArgument);
  const htmlCache = new Map();
  for (const locale of Object.keys(model.manifest.editions)) {
    const relativeIndex = searchIndexOutputPath(model, locale).replace(/^docs\//u, '');
    const indexFile = path.join(siteRoot, relativeIndex);
    const index = readIndex(indexFile, errors);
    validateIndex(index, locale, pageDescriptors(model, locale), errors);
    for (const entry of index?.entries || []) {
      const target = siteFileForUrl(siteRoot, entry.url);
      if (!target.file || !fs.existsSync(target.file)) {
        errors.push(`${locale}: missing built page for ${entry.url}`);
        continue;
      }
      if (!target.fragment) continue;
      let ids = htmlCache.get(target.file);
      if (!ids) {
        ids = htmlIds(fs.readFileSync(target.file, 'utf8'));
        htmlCache.set(target.file, ids);
      }
      if (!ids.has(target.fragment)) errors.push(`${locale}: missing built anchor ${entry.url}`);
    }
  }

  for (const [relative, locale] of [['index.html', 'ja'], ['en/index.html', 'en']]) {
    const file = path.join(siteRoot, relative);
    if (!fs.existsSync(file)) {
      errors.push(`site: missing ${relative}`);
      continue;
    }
    const html = fs.readFileSync(file, 'utf8');
    for (const marker of ['role="combobox"', 'role="listbox"', 'aria-live="polite"', 'data-index-url=']) {
      if (!html.includes(marker)) errors.push(`${relative}: missing search marker ${marker}`);
    }
    const localePath = locale === 'ja' ? '' : '/en';
    for (const marker of [
      '<nav class="sidebar-nav"',
      'maxlength="128"',
      `data-index-url="/${model.manifest.project.id}/assets/search-index.${locale}.json"`,
      `href="/${model.manifest.project.id}${localePath}/glossary/"`,
    ]) {
      if (!html.includes(marker)) errors.push(`${relative}: JS-independent navigation marker is missing: ${marker}`);
    }
    const glossaryFile = path.join(siteRoot, locale === 'ja' ? 'glossary/index.html' : 'en/glossary/index.html');
    if (!fs.existsSync(glossaryFile)) errors.push(`${relative}: JS-independent glossary page is missing`);
  }
  for (const asset of ['assets/js/search.js', 'assets/css/main.css', 'assets/search-index.ja.json', 'assets/search-index.en.json']) {
    const file = path.join(siteRoot, asset);
    if (!fs.existsSync(file) || fs.statSync(file).size === 0) errors.push(`site: missing asset ${asset}`);
  }

  fail(errors);
  console.log(`Built-site search smoke passed: ${htmlCache.size} pages and all indexed anchors verified.`);
}

const siteIndex = process.argv.indexOf('--site');
if (siteIndex !== -1) {
  const siteArgument = process.argv[siteIndex + 1];
  if (!siteArgument) throw new Error('Usage: node scripts/check-search-index.js --site <jekyll-output>');
  checkSite(siteArgument);
} else {
  checkGenerated();
}
