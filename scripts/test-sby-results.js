#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  parseSbyStatus,
  validateExpected,
  validateSbyResults,
  writeResults,
} = require('./validate-sby-results');

const REPO_ROOT = path.resolve(__dirname, '..');
const exampleRoot = path.join(REPO_ROOT, 'examples/ch08/sby/rtl-arbiter');
const flawed = JSON.parse(fs.readFileSync(path.join(exampleRoot, 'expected-flawed-bmc.json'), 'utf8'));
const prove = JSON.parse(fs.readFileSync(path.join(exampleRoot, 'expected-fixed-prove.json'), 'utf8'));
const cover = JSON.parse(fs.readFileSync(path.join(exampleRoot, 'expected-fixed-cover.json'), 'utf8'));
const raw = (status, rc, task = 'bmc', step = 3) => {
  const details = task === 'prove'
    ? 'SBY 12:00:00 [arbiter] engine_0.basecase: Status returned by engine for basecase: pass\nSBY 12:00:00 [arbiter] engine_0.induction: Status returned by engine for induction: pass\n'
    : task === 'bmc'
      ? `SBY 12:00:00 [arbiter] summary: failed assertion arbiter.check at arbiter.sv:1 step ${step}\n`
      : `SBY 12:00:00 [arbiter] summary: reached cover statement arbiter.check at arbiter.sv:1 step ${step}\n`;
  return `SBY 12:00:00 [arbiter] engine_0: smtbmc bitwuzla\nSBY 12:00:00 [arbiter] depth: 6\n${details}SBY 12:00:00 [arbiter] DONE (${status}, rc=${rc})\n`;
};

function makeWork(parent, name, { trace = false } = {}) {
  const work = path.join(parent, name);
  fs.mkdirSync(path.join(work, 'engine_0'), { recursive: true });
  if (trace) fs.writeFileSync(path.join(work, 'engine_0', 'trace.vcd'), '$comment SBY trace $end\n');
  return work;
}

assert.deepStrictEqual(parseSbyStatus(raw('FAIL', 2)), { status: 'FAIL', returnCode: 2 });
validateExpected(flawed);
validateExpected(prove);
validateExpected(cover);
assert.throws(() => validateExpected({ ...flawed, status: 'PASS' }), /status\/result/);
assert.throws(() => validateExpected({ ...cover, trace: { required: true, kind: 'counterexample', step: 3 } }), /trace kind/);
assert.throws(() => validateExpected({ ...prove, trace: { required: true } }), /trace requirement/);

const fixtureParent = path.join(REPO_ROOT, 'tools/.tmp');
fs.mkdirSync(fixtureParent, { recursive: true });
const temp = fs.mkdtempSync(path.join(fixtureParent, 'sby-result-test-'));
try {
  const bmcWork = makeWork(temp, 'bmc', { trace: true });
  const bmc = validateSbyResults({ raw: raw('FAIL', 2), expected: flawed, workDir: bmcWork });
  assert.strictEqual(bmc.traces.length, 1);
  assert.throws(() => validateSbyResults({ raw: raw('PASS', 0), expected: flawed, workDir: bmcWork }), /status mismatch/);
  assert.throws(() => validateSbyResults({ raw: raw('FAIL', 1), expected: flawed, workDir: bmcWork }), /return code mismatch/);
  const missingTrace = makeWork(temp, 'missing');
  assert.throws(() => validateSbyResults({ raw: raw('FAIL', 2), expected: flawed, workDir: missingTrace }), /exactly one/);
  fs.writeFileSync(path.join(bmcWork, 'engine_0', 'wrong.vcd'), '$end\n');
  assert.throws(() => validateSbyResults({ raw: raw('FAIL', 2), expected: flawed, workDir: bmcWork }), /exactly one/);

  const proveWork = makeWork(temp, 'prove');
  assert.doesNotThrow(() => validateSbyResults({ raw: raw('PASS', 0, 'prove'), expected: prove, workDir: proveWork }));
  const failedInduction = raw('PASS', 0, 'prove').replace('engine for induction: pass', 'engine for induction: fail');
  assert.throws(() => validateSbyResults({ raw: failedInduction, expected: prove, workDir: proveWork }), /basecase and induction/);

  const coverWork = makeWork(temp, 'cover', { trace: true });
  assert.doesNotThrow(() => validateSbyResults({ raw: raw('PASS', 0, 'cover'), expected: cover, workDir: coverWork }));
  assert.throws(() => validateSbyResults({ raw: raw('PASS', 0, 'cover', 4), expected: cover, workDir: coverWork }), /trace step mismatch/);

  const expectedPath = path.join(temp, 'expected.json');
  const resultsPath = path.join(temp, 'results.json');
  const summaryPath = path.join(temp, 'summary.log');
  const rawPath = path.join(temp, 'raw.log');
  fs.writeFileSync(expectedPath, JSON.stringify(cover));
  fs.writeFileSync(rawPath, raw('PASS', 0, 'cover'));
  const generated = writeResults({ rawPath, expectedPath, workDir: coverWork, resultsPath, summaryPath, repoRoot: REPO_ROOT, timeLimitSeconds: 240 });
  assert.strictEqual(generated.result.result, 'covered');
  assert.strictEqual(generated.result.trace.kind, 'cover');
  assert.match(fs.readFileSync(summaryPath, 'utf8'), /Bitwuzla 0\.9\.1/);
  assert.match(fs.readFileSync(resultsPath, 'utf8'), /55dd70cdfc9a5d76711806f2822300c0755c2a5b/);
} finally {
  fs.rmSync(temp, { recursive: true, force: true });
}

console.log('SBY result contract tests passed (BMC, proof, cover, status, trace, and artifacts).');
