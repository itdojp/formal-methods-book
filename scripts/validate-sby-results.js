#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { getTool, loadToolManifest } = require('./tool-manifest');

const VALID_TASKS = new Set(['bmc', 'prove', 'cover']);
const VALID_STATUSES = new Set(['PASS', 'FAIL']);
const VALID_RESULTS = new Set(['counterexample', 'proved', 'covered']);

function readJson(filePath, label) {
  try {
    return JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (error) {
    throw new Error(`${label} is not valid JSON: ${error.message}`);
  }
}

function validateExpected(expected) {
  if (!expected || typeof expected !== 'object' || Array.isArray(expected)) throw new Error('expected contract must be an object');
  if (expected.schemaVersion !== 1) throw new Error('expected schemaVersion must be 1');
  if (!VALID_TASKS.has(expected.task) || expected.mode !== expected.task) throw new Error('expected task/mode must be bmc, prove, or cover');
  if (!Number.isSafeInteger(expected.depth) || expected.depth < 1 || expected.depth > 1000) throw new Error('expected depth must be an integer in 1..1000');
  if (!VALID_STATUSES.has(expected.status)) throw new Error('expected status must be PASS or FAIL');
  if (!VALID_RESULTS.has(expected.result)) throw new Error('expected result is invalid');
  const expectedResult = expected.task === 'bmc' ? 'counterexample' : expected.task === 'prove' ? 'proved' : 'covered';
  const expectedStatus = expected.task === 'bmc' ? 'FAIL' : 'PASS';
  if (expected.result !== expectedResult || expected.status !== expectedStatus) throw new Error('expected status/result do not match the task contract');
  if (!expected.trace || typeof expected.trace !== 'object' || Array.isArray(expected.trace)) throw new Error('expected trace must be an object');
  if (typeof expected.trace.required !== 'boolean') throw new Error('expected trace.required must be boolean');
  if (expected.trace.required !== (expected.task !== 'prove')) throw new Error('trace requirement does not match task contract');
  if (expected.trace.required) {
    if (!['counterexample', 'cover'].includes(expected.trace.kind) || !Number.isSafeInteger(expected.trace.step) || expected.trace.step < 0) {
      throw new Error('required trace must declare kind and non-negative step');
    }
    if ((expected.task === 'bmc' && expected.trace.kind !== 'counterexample') || (expected.task === 'cover' && expected.trace.kind !== 'cover')) {
      throw new Error('trace kind does not match task');
    }
  }
}

function parseSbyStatus(raw) {
  const matches = Array.from(raw.matchAll(/\bDONE \((PASS|FAIL), rc=([0-9]+)\)/g));
  if (matches.length !== 1) throw new Error(`expected exactly one SBY DONE status, found ${matches.length}`);
  return { status: matches[0][1], returnCode: Number(matches[0][2]) };
}

function parseDepth(raw) {
  const matches = Array.from(raw.matchAll(/\b(?:depth|Depth)\s*[:=]\s*(\d+)\b/g));
  if (matches.length === 0) return null;
  const values = new Set(matches.map((match) => Number(match[1])));
  if (values.size !== 1) throw new Error('SBY output reported conflicting depth values');
  return [...values][0];
}

function proofStatuses(raw) {
  const phases = { basecase: [], induction: [] };
  const pattern = /engine_\d+\.(basecase|induction): Status returned by engine for (basecase|induction): (pass|fail)\b/gi;
  for (const match of raw.matchAll(pattern)) {
    if (match[1].toLowerCase() !== match[2].toLowerCase()) {
      throw new Error(`conflicting SBY proof phase labels: ${match[1]}/${match[2]}`);
    }
    phases[match[1].toLowerCase()].push(match[3].toUpperCase());
  }
  for (const phase of ['basecase', 'induction']) {
    if (phases[phase].length !== 1) throw new Error(`expected exactly one ${phase} engine status, found ${phases[phase].length}`);
  }
  return { base: phases.basecase[0], induction: phases.induction[0] };
}

function parseTraceStep(raw, task) {
  if (task === 'prove') return null;
  const label = task === 'bmc' ? 'failed assertion' : 'reached cover statement';
  const pattern = new RegExp(`\\bsummary:\\s+${label}[^\\n]*\\bstep (\\d+)\\s*$`, 'gmi');
  const steps = Array.from(raw.matchAll(pattern), (match) => Number(match[1]));
  if (steps.length !== 1) throw new Error(`expected exactly one ${task} trace-step summary, found ${steps.length}`);
  return steps[0];
}

function listVcds(rootDir) {
  const result = [];
  function visit(directory) {
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      const item = path.join(directory, entry.name);
      if (entry.isDirectory()) visit(item);
      else if (entry.isFile() && entry.name.endsWith('.vcd')) result.push(item);
      else if (entry.isSymbolicLink()) throw new Error(`unexpected symbolic link in SBY work directory: ${item}`);
    }
  }
  if (fs.existsSync(rootDir)) visit(rootDir);
  return result.sort();
}

function validateSbyResults({ raw, expected, workDir }) {
  validateExpected(expected);
  const actual = parseSbyStatus(raw);
  if (actual.status !== expected.status) throw new Error(`SBY status mismatch: expected ${expected.status}, got ${actual.status}`);
  const expectedRc = expected.status === 'PASS' ? 0 : 2;
  if (actual.returnCode !== expectedRc) throw new Error(`SBY return code mismatch: expected ${expectedRc}, got ${actual.returnCode}`);
  const outputDepth = parseDepth(raw);
  if (outputDepth !== null && outputDepth !== expected.depth) throw new Error(`SBY depth mismatch: expected ${expected.depth}, got ${outputDepth}`);
  const proof = expected.task === 'prove' ? proofStatuses(raw) : null;
  if (expected.task === 'prove' && (proof.base !== 'PASS' || proof.induction !== 'PASS')) {
    throw new Error(`prove requires PASS basecase and induction status, got ${String(proof.base)}/${String(proof.induction)}`);
  }
  const traceStep = parseTraceStep(raw, expected.task);
  if (expected.trace.required && traceStep !== expected.trace.step) {
    throw new Error(`SBY trace step mismatch: expected ${expected.trace.step}, got ${traceStep}`);
  }
  const traces = listVcds(workDir);
  if (expected.trace.required && traces.length !== 1) throw new Error(`expected exactly one ${expected.trace.kind} VCD trace, found ${traces.length}`);
  if (!expected.trace.required && traces.length !== 0) throw new Error(`proof must not retain a VCD trace, found ${traces.length}`);
  return { actual, outputDepth, proof, traceStep, traces };
}

function writeResults(options) {
  const expected = readJson(options.expectedPath, 'expected contract');
  const raw = fs.readFileSync(options.rawPath, 'utf8');
  const actual = validateSbyResults({ raw, expected, workDir: options.workDir });
  const { manifest } = loadToolManifest(options.repoRoot);
  const tool = getTool(manifest, 'sby');
  if (!tool) throw new Error('sby tool manifest entry was not found');
  const trace = actual.traces.length === 0 ? null : {
    kind: expected.trace.kind,
    step: actual.traceStep,
    source: path.relative(options.workDir, actual.traces[0]).split(path.sep).join('/'),
    retained: 'trace.vcd',
  };
  const result = {
    schemaVersion: 1,
    tool: 'SymbiYosys (sby)',
    suite: { version: tool.suiteVersion, commit: tool.suiteCommit, digest: tool.distribution.sha256, distribution: tool.distribution },
    sby: { version: tool.version, commit: tool.commit },
    yosys: { version: tool.yosysVersion, commit: tool.yosysCommit },
    bitwuzla: { version: tool.bitwuzlaVersion, commit: tool.bitwuzlaCommit },
    mode: expected.mode,
    task: expected.task,
    depth: expected.depth,
    timeoutSeconds: options.timeLimitSeconds,
    status: actual.actual.status,
    result: expected.result,
    proof: actual.proof,
    trace,
  };
  fs.writeFileSync(options.resultsPath, `${JSON.stringify(result, null, 2)}\n`);
  const summary = [
    `OSS CAD Suite ${tool.suiteVersion} (${tool.suiteCommit})`,
    `SymbiYosys ${tool.version} (${tool.commit})`,
    `Yosys ${tool.yosysVersion} (${tool.yosysCommit})`,
    `Bitwuzla ${tool.bitwuzlaVersion} (${tool.bitwuzlaCommit})`,
    `task: ${expected.task}; mode: ${expected.mode}; depth: ${expected.depth}; timeout: ${options.timeLimitSeconds}s`,
    `status: ${actual.actual.status}; result: ${expected.result}`,
    expected.task === 'prove' ? `proof: basecase=${actual.proof.base}; induction=${actual.proof.induction}` : `trace: ${trace.kind}; step=${trace.step}; retained=${trace.retained}`,
  ];
  fs.writeFileSync(options.summaryPath, `${summary.join('\n')}\n`);
  return { result, traceSource: actual.traces[0] || null };
}

function main(argv) {
  if (argv.length !== 7 || !/^[1-9]\d*$/.test(argv[6])) {
    console.error('Usage: validate-sby-results.js RAW EXPECTED WORK_DIR RESULTS SUMMARY REPO_ROOT TIME_LIMIT_SECONDS');
    process.exitCode = 2;
    return;
  }
  try {
    writeResults({ rawPath: argv[0], expectedPath: argv[1], workDir: argv[2], resultsPath: argv[3], summaryPath: argv[4], repoRoot: argv[5], timeLimitSeconds: Number(argv[6]) });
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}

if (require.main === module) main(process.argv.slice(2));
module.exports = { listVcds, parseDepth, parseSbyStatus, parseTraceStep, proofStatuses, validateExpected, validateSbyResults, writeResults };
