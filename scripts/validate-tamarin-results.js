#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { getTool, loadToolManifest } = require('./tool-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');
const VALID_MODES = new Set(['exists-trace', 'all-traces']);
const VALID_STATUSES = new Set(['verified', 'falsified']);
const VALID_RESULTS = new Set(['verified', 'attack-found']);

function loadJson(filePath, label) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    throw new Error(`${label} is not valid JSON: ${error.message}`);
  }
}

function validateExpected(expected) {
  if (!expected || typeof expected !== 'object' || Array.isArray(expected)) {
    throw new Error('expected-results contract must be an object');
  }
  if (expected.schemaVersion !== 1) throw new Error('expected-results schemaVersion must be 1');
  if (!VALID_RESULTS.has(expected.result)) throw new Error(`invalid expected result: ${String(expected.result)}`);
  if (!Array.isArray(expected.lemmas) || expected.lemmas.length === 0) {
    throw new Error('expected-results lemmas must be a non-empty array');
  }
  const names = new Set();
  for (const lemma of expected.lemmas) {
    if (!lemma || typeof lemma !== 'object' || Array.isArray(lemma)) throw new Error('each expected lemma must be an object');
    if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(lemma.name || '')) throw new Error(`invalid expected lemma name: ${String(lemma.name)}`);
    if (names.has(lemma.name)) throw new Error(`duplicate expected lemma: ${lemma.name}`);
    names.add(lemma.name);
    if (!VALID_MODES.has(lemma.mode)) throw new Error(`invalid expected lemma mode for ${lemma.name}: ${String(lemma.mode)}`);
    if (!VALID_STATUSES.has(lemma.status)) throw new Error(`invalid expected lemma status for ${lemma.name}: ${String(lemma.status)}`);
  }
  const falsified = expected.lemmas.filter((lemma) => lemma.status === 'falsified');
  if (expected.result === 'verified') {
    if (falsified.length !== 0 || expected.attackLemma !== null) {
      throw new Error('verified contract cannot contain a falsified lemma or attackLemma');
    }
  } else if (falsified.length !== 1 || expected.attackLemma !== falsified[0].name) {
    throw new Error('attack-found contract must name its single falsified lemma as attackLemma');
  }
}

function parseSummary(raw) {
  const marker = 'summary of summaries:';
  const start = raw.lastIndexOf(marker);
  if (start < 0) throw new Error('Tamarin summary marker was not found');
  const summary = raw.slice(start + marker.length);
  const pattern = /^\s{2}([A-Za-z][A-Za-z0-9_]*) \((exists-trace|all-traces)\): (verified|falsified - found trace) \((\d+) steps?\)\s*$/gm;
  const lemmas = [];
  for (const match of summary.matchAll(pattern)) {
    lemmas.push({
      name: match[1],
      mode: match[2],
      status: match[3].startsWith('falsified') ? 'falsified' : 'verified',
      steps: Number(match[4]),
    });
  }
  if (lemmas.length === 0) throw new Error('Tamarin summary contained no recognized lemma results');
  return lemmas;
}

function compareLemmas(actual, expected) {
  if (actual.length !== expected.length) {
    throw new Error(`lemma count mismatch: expected ${expected.length}, got ${actual.length}`);
  }
  for (let index = 0; index < expected.length; index += 1) {
    const wanted = expected[index];
    const got = actual[index];
    for (const field of ['name', 'mode', 'status']) {
      if (got[field] !== wanted[field]) {
        throw new Error(`lemma ${index + 1} ${field} mismatch: expected ${wanted[field]}, got ${got[field]}`);
      }
    }
  }
}

function selectAttackGraph(graphDocument, attackLemma) {
  if (!graphDocument || typeof graphDocument !== 'object' || !Array.isArray(graphDocument.graphs)) {
    throw new Error('Tamarin graph output must contain a graphs array');
  }
  if (attackLemma === null) return null;
  const matches = graphDocument.graphs.filter(
    (graph) => typeof graph?.jgLabel === 'string' && graph.jgLabel.includes(`_${attackLemma}`),
  );
  if (matches.length !== 1) {
    throw new Error(`expected exactly one ${attackLemma} attack graph, got ${matches.length}`);
  }
  return matches[0];
}

function writeResults(options) {
  const expected = loadJson(options.expectedPath, 'expected-results contract');
  validateExpected(expected);
  const actual = parseSummary(fs.readFileSync(options.rawLogPath, 'utf8'));
  compareLemmas(actual, expected.lemmas);
  const graphDocument = loadJson(options.rawGraphPath, 'Tamarin graph output');
  const attackGraph = selectAttackGraph(graphDocument, expected.attackLemma);
  const { manifest } = loadToolManifest(options.repoRoot || REPO_ROOT);
  const tool = getTool(manifest, 'tamarin');
  if (!tool) throw new Error('Tamarin tool manifest entry was not found');

  const proof = {
    mode: 'automated',
    options: ['--quit-on-warning', '--prove', '--stop-on-trace=SEQDFS', '--output-json'],
    timeLimitSeconds: options.timeLimitSeconds,
    timeoutEnforcement: 'coreutils-timeout-and-manifest-runner',
  };
  const result = {
    schemaVersion: 1,
    result: expected.result,
    model: path.basename(options.modelPath),
    tamarin: {
      version: tool.version,
      commit: tool.commit,
      distribution: tool.distribution,
    },
    maude: {
      version: tool.maudeVersion,
      commit: tool.maudeCommit,
      distribution: tool.maudeDistribution,
    },
    proof,
    lemmas: actual,
    attackLemma: expected.attackLemma,
  };
  fs.writeFileSync(options.resultsPath, `${JSON.stringify(result, null, 2)}\n`);

  const summaryLines = [
    `Tamarin Prover ${tool.version} (${tool.commit})`,
    `Maude ${tool.maudeVersion} (${tool.maudeCommit})`,
    `model: ${path.basename(options.modelPath)}`,
    `proof: automated; time limit ${options.timeLimitSeconds}s; ${proof.options.join(' ')}`,
    ...actual.map((lemma) => `${lemma.name} (${lemma.mode}): ${lemma.status} (${lemma.steps} steps)`),
    `result: ${expected.result}`,
  ];
  fs.writeFileSync(options.summaryPath, `${summaryLines.join('\n')}\n`);

  if (attackGraph) {
    fs.writeFileSync(options.attackPath, `${JSON.stringify({
      schemaVersion: 1,
      lemma: expected.attackLemma,
      model: path.basename(options.modelPath),
      graph: attackGraph,
    }, null, 2)}\n`);
  } else {
    fs.rmSync(options.attackPath, { force: true });
  }
  return result;
}

function main(argv) {
  if (argv.length !== 8 || !/^\d+$/.test(argv[7]) || Number(argv[7]) <= 0) {
    console.error('Usage: validate-tamarin-results.js RAW_LOG RAW_GRAPH MODEL EXPECTED RESULTS SUMMARY ATTACK TIME_LIMIT_SECONDS');
    process.exitCode = 2;
    return;
  }
  try {
    writeResults({
      rawLogPath: argv[0],
      rawGraphPath: argv[1],
      modelPath: argv[2],
      expectedPath: argv[3],
      resultsPath: argv[4],
      summaryPath: argv[5],
      attackPath: argv[6],
      timeLimitSeconds: Number(argv[7]),
      repoRoot: REPO_ROOT,
    });
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}

if (require.main === module) main(process.argv.slice(2));

module.exports = {
  compareLemmas,
  parseSummary,
  selectAttackGraph,
  validateExpected,
  writeResults,
};
