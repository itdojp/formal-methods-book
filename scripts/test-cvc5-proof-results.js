#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  TINY_QF_UF_CONTRADICTION,
  classifyChecker,
  parseSolverEnvelope,
  solverResult,
  validateTinySmt2,
  writeResults,
} = require('./validate-cvc5-proof-results');

const REPO_ROOT = path.resolve(__dirname, '..');
const proof = [
  'unsat',
  '(',
  '(assume a0 p)',
  '(assume a1 (! (not p) :named @p_1))',
  '(step t0 (cl) :rule resolution :premises (a0 a1))',
  ')',
  '',
].join('\n');
const oversizedProof = `unsat\n(${` ${'x'.repeat(1100)}`})\n`;

assert.deepStrictEqual(validateTinySmt2(TINY_QF_UF_CONTRADICTION).assertions, ['p', '(not p)']);
assert.throws(
  () => validateTinySmt2(TINY_QF_UF_CONTRADICTION.replace('(check-sat)', '(get-model)')),
  /exact self-contained QF_UF Bool contradiction teaching grammar/,
  'dangerous SMT-LIB output commands must be rejected before bootstrap',
);
assert.strictEqual(parseSolverEnvelope(proof, 1024).certificate.includes(':rule resolution'), true);
assert.strictEqual(parseSolverEnvelope('sat\n', 1024).status, 'sat');
assert.throws(() => parseSolverEnvelope('sat\n(model)\n', 1024), /additional output channel/);
assert.throws(() => parseSolverEnvelope(oversizedProof, 1024), /exceeds/);
assert.throws(() => parseSolverEnvelope('unsat\n(step bad)\ntrailing\n', 1024), /one parenthesized expression/);
assert.strictEqual(solverResult({ solverStatus: 0, raw: 'sat\n', maxCertificateBytes: 1024 }).result, 'solver-sat');
assert.strictEqual(solverResult({ solverStatus: 0, raw: 'unknown\n', maxCertificateBytes: 1024 }).result, 'solver-unknown');
assert.strictEqual(solverResult({ solverStatus: 124, raw: '', maxCertificateBytes: 1024 }).result, 'solver-timeout');
assert.strictEqual(solverResult({ solverStatus: 0, raw: oversizedProof, maxCertificateBytes: 1024 }).result, 'proof-too-large');
assert.strictEqual(classifyChecker(0, 'valid\n'), 'success');
assert.strictEqual(classifyChecker(124, ''), 'checker-timeout');
assert.strictEqual(classifyChecker(125, ''), 'checker-output-too-large');
assert.strictEqual(classifyChecker(1, 'error: unknown rule corrupt-rule\n'), 'checker-unknown');
assert.strictEqual(classifyChecker(1, 'error: proof contains hole\n'), 'checker-holey');
assert.strictEqual(classifyChecker(1, 'invalid proof\n'), 'checker-invalid');

const fixtureParent = path.join(REPO_ROOT, 'tools/.tmp');
fs.mkdirSync(fixtureParent, { recursive: true });
const fixture = fs.mkdtempSync(path.join(fixtureParent, 'cvc5-result-test-'));
try {
  const input = path.join(fixture, 'contradiction.smt2');
  const raw = path.join(fixture, 'solver.raw');
  const checker = path.join(fixture, 'checker.raw');
  const results = path.join(fixture, 'results.json');
  const summary = path.join(fixture, 'summary.log');
  fs.writeFileSync(input, TINY_QF_UF_CONTRADICTION);
  fs.writeFileSync(raw, proof);
  fs.writeFileSync(checker, 'valid\n');
  const valid = writeResults({
    inputPath: input, solverRawPath: raw, checkerRawPath: checker, solverStatus: 0, checkerStatus: 0,
    resultsPath: results, summaryPath: summary, repoRoot: REPO_ROOT, timeLimitSeconds: 120,
  });
  assert.strictEqual(valid.result, 'success');
  assert.strictEqual(valid.certificateFormat, 'alethe');
  assert.match(fs.readFileSync(summary, 'utf8'), /result: success/);
  fs.writeFileSync(checker, 'x'.repeat(valid.checker.maxOutputBytes));
  const oversizedChecker = writeResults({
    inputPath: input, solverRawPath: raw, checkerRawPath: checker, solverStatus: 0, checkerStatus: 1,
    resultsPath: results, summaryPath: summary, repoRoot: REPO_ROOT, timeLimitSeconds: 120,
  });
  assert.strictEqual(oversizedChecker.result, 'checker-output-too-large');
  assert.strictEqual(oversizedChecker.evidence.checkerOutputBytes, valid.checker.maxOutputBytes);
  assert.strictEqual(oversizedChecker.evidence.checkerOutputSha256, null);
  fs.writeFileSync(raw, 'sat\n');
  const sat = writeResults({
    inputPath: input, solverRawPath: raw, checkerRawPath: checker, solverStatus: 0, checkerStatus: -1,
    resultsPath: results, summaryPath: summary, repoRoot: REPO_ROOT, timeLimitSeconds: 120,
  });
  assert.strictEqual(sat.result, 'solver-sat');
  assert.strictEqual(sat.evidence.certificate, null);
} finally {
  fs.rmSync(fixture, { recursive: true, force: true });
}

console.log('cvc5 proof-result tests passed (grammar, strict envelopes, non-success taxonomy, and provenance).');
