#!/usr/bin/env node
/*
  Bilingual builder.
  - JA publish root stays at docs/
  - EN publish root stays at docs/en/
  - Publication metadata is generated from edition configs before content
  - JA and EN public Markdown pages are generated from src/<locale>/**
*/
const path = require('path');
const {
  loadPublicationModel,
  renderGeneratedArtifacts,
  writeGeneratedArtifacts,
} = require('./lib/publication-metadata');
const {
  renderEditionPages,
  writeEditionPages,
} = require('./lib/publication-build');
const { writeSearchIndex } = require('./lib/search-index');

const repoRoot = path.resolve(__dirname, '..');
const target = process.argv[2] || 'all';
const validTargets = new Set(['ja', 'en', 'all']);

if (!validTargets.has(target)) {
  console.error(`Unsupported build target: ${target}`);
  console.error('Usage: node scripts/build.js [ja|en|all]');
  process.exit(1);
}

function buildEdition(locale) {
  const pages = renderEditionPages(repoRoot, publicationModel, locale);
  writeEditionPages(repoRoot, publicationModel, locale, pages);
  console.log(`Built ${pages.size} ${locale} pages into ${publicationModel.manifest.editions[locale].publishRoot}.`);
  const search = writeSearchIndex(repoRoot, publicationModel, locale, pages);
  console.log(`Built ${search.entries} ${locale} search entries (${search.bytes} bytes) in ${search.elapsedMs.toFixed(1)} ms at ${search.outputPath}.`);
}

const publicationModel = loadPublicationModel(repoRoot);
writeGeneratedArtifacts(repoRoot, renderGeneratedArtifacts(publicationModel));

if (target === 'all') {
  buildEdition('ja');
  buildEdition('en');
} else {
  buildEdition(target);
}
