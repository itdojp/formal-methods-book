#!/usr/bin/env node
'use strict';

const path = require('path');
const {
  compareGeneratedArtifacts,
  loadPublicationModel,
  renderGeneratedArtifacts,
  writeGeneratedArtifacts,
} = require('./lib/publication-metadata');

const repoRoot = path.resolve(__dirname, '..');
const checkOnly = process.argv.includes('--check');
const unexpectedArguments = process.argv.slice(2).filter((argument) => argument !== '--check');

if (unexpectedArguments.length > 0) {
  console.error(`Unsupported arguments: ${unexpectedArguments.join(' ')}`);
  console.error('Usage: node scripts/generate-publication-metadata.js [--check]');
  process.exit(2);
}

try {
  const model = loadPublicationModel(repoRoot);
  const artifacts = renderGeneratedArtifacts(model);
  if (checkOnly) {
    const differences = compareGeneratedArtifacts(repoRoot, artifacts);
    if (differences.length > 0) {
      console.error('Generated publication metadata is stale:');
      for (const difference of differences) console.error(`- ${difference}`);
      console.error('Run npm run generate:metadata and commit the generated artifacts.');
      process.exit(1);
    }
    console.log(`Publication metadata is current (${artifacts.size} artifacts).`);
  } else {
    writeGeneratedArtifacts(repoRoot, artifacts);
    console.log(`Generated ${artifacts.size} publication metadata artifacts.`);
  }
} catch (error) {
  console.error(error.message);
  process.exit(1);
}
