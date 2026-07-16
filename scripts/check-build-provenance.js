#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const {
  DEFAULT_OUTPUT,
  readJson,
  sameJsonValue,
  validateBuildProvenance,
} = require('./lib/build-provenance');

const repoRoot = path.resolve(__dirname, '..');
const args = process.argv.slice(2);
let siteRoot = null;
if (args.length === 2 && args[0] === '--site') {
  siteRoot = path.resolve(repoRoot, args[1]);
} else if (args.length !== 0) {
  console.error('Usage: node scripts/check-build-provenance.js [--site SITE_DIR]');
  process.exit(2);
}

function fail(message) {
  console.error(`Build provenance check failed: ${message}`);
  process.exit(1);
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function assertMarker(html, marker, filePath) {
  if (!html.includes(marker)) fail(`${filePath}: missing ${marker}`);
}

function assertNoMarker(html, marker, filePath) {
  if (html.includes(marker)) fail(`${filePath}: unexpected ${marker}`);
}

function readerHtmlPaths() {
  const basePath = '/formal-methods-book/';
  const paths = new Set();
  for (const locale of ['ja', 'en']) {
    const index = readJson(path.join(repoRoot, `docs/assets/search-index.${locale}.json`));
    for (const entry of index.entries || []) {
      const url = new URL(entry.url, 'https://itdojp.github.io');
      if (!url.pathname.startsWith(basePath)) fail(`${locale} search URL is outside ${basePath}: ${entry.url}`);
      const relative = url.pathname.slice(basePath.length).replace(/^\/+|\/+$/g, '');
      paths.add(path.join(siteRoot, relative, 'index.html'));
    }
  }
  return [...paths].sort();
}

try {
  const manifest = readJson(path.join(repoRoot, 'book-config.json'));
  const provenancePath = path.join(repoRoot, DEFAULT_OUTPUT);
  if (!fs.existsSync(provenancePath)) fail(`${DEFAULT_OUTPUT} is missing; run npm run generate:provenance`);
  const provenance = readJson(provenancePath);
  const errors = validateBuildProvenance(provenance, manifest, {
    requireRun: Boolean(siteRoot),
    repoRoot,
  });
  if (errors.length > 0) fail(errors.join('; '));

  if (!siteRoot) {
    console.log(`Build provenance data is valid for ${provenance.version} at ${provenance.source_commit}.`);
    process.exit(0);
  }
  if (!fs.statSync(siteRoot).isDirectory()) fail(`site directory not found: ${siteRoot}`);

  const publicJsonPath = path.join(siteRoot, 'build-provenance.json');
  if (!fs.existsSync(publicJsonPath)) fail('built build-provenance.json is missing');
  const publicPayload = readJson(publicJsonPath);
  if (!sameJsonValue(publicPayload, provenance)) fail('public build-provenance.json differs from Jekyll input data');

  const htmlPaths = readerHtmlPaths();
  if (htmlPaths.length !== 46) fail(`expected 46 JA/EN reader pages, found ${htmlPaths.length}`);
  for (const htmlPath of htmlPaths) {
    if (!fs.existsSync(htmlPath)) fail(`reader page is missing: ${path.relative(siteRoot, htmlPath)}`);
    const html = fs.readFileSync(htmlPath, 'utf8');
    const relative = path.relative(siteRoot, htmlPath);
    assertMarker(html, `<meta name="book-version" content="${provenance.version}">`, relative);
    assertMarker(html, `<meta name="book-source-commit" content="${provenance.source_commit}">`, relative);
    assertMarker(html, `<meta name="book-generated-at" content="${provenance.generated_at}">`, relative);
    if (provenance.release_url) {
      assertMarker(html, `<meta name="book-release" content="${provenance.release_url}">`, relative);
      assertMarker(html, `href="${provenance.release_url}"`, relative);
    } else {
      assertNoMarker(html, '<meta name="book-release"', relative);
    }
    assertMarker(html, `<meta name="book-pages-run" content="${provenance.pages_run_url}">`, relative);
    assertMarker(html, `data-book-version="${provenance.version}"`, relative);
    assertMarker(html, `data-source-commit="${provenance.source_commit}"`, relative);
    assertMarker(html, `data-generated-at="${provenance.generated_at}"`, relative);
    if (!new RegExp(`href="${escapeRegExp(provenance.source_url)}"`).test(html)) fail(`${relative}: source commit link is missing`);
  }

  console.log(`Build provenance is present on ${htmlPaths.length} reader pages and the public JSON endpoint.`);
} catch (error) {
  fail(error.message);
}
