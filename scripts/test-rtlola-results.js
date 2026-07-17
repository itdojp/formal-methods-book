#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  EXPECTED_SPEC,
  MAX_OUTPUT_BYTES,
  parseContract,
  parseRtlolaOutput,
  parseTrace,
  validateRtlolaResults,
  validateSpec,
} = require('./validate-rtlola-results');

const repoRoot = path.resolve(__dirname, '..');
const exampleRoot = path.join(repoRoot, 'examples/runtime-verification/auth-before-sensitive');
const normalTrace = fs.readFileSync(path.join(exampleRoot, 'normal.csv'), 'utf8');
const violationTrace = fs.readFileSync(path.join(exampleRoot, 'violation.csv'), 'utf8');
const normalContract = JSON.parse(fs.readFileSync(path.join(exampleRoot, 'expected-normal.json'), 'utf8'));
const violationContract = JSON.parse(fs.readFileSync(path.join(exampleRoot, 'expected-violation.json'), 'utf8'));
const violationOutput = '{"time":"1.000000000","trigger_0":[{"eval":"AUTH_BEFORE_SENSITIVE violated"}]}\n';
const provenance = {
  toolVersion: '0.1.2',
  toolCommit: '11b6bb080a5fa487645fb023fb3d0baea6874e73',
  rustToolchain: '1.87.0',
  timeLimitSeconds: 60,
};

function expectFailure(action, pattern) {
  assert.throws(action, pattern);
}

validateSpec(EXPECTED_SPEC);
assert.strictEqual(parseTrace(normalTrace).length, 3);
assert.deepStrictEqual(parseRtlolaOutput(''), []);
assert.deepStrictEqual(parseRtlolaOutput(violationOutput), [
  { time: '1.000000000', message: 'AUTH_BEFORE_SENSITIVE violated' },
]);
parseContract(normalContract);
parseContract(violationContract);

const normal = validateRtlolaResults({
  specText: EXPECTED_SPEC,
  traceText: normalTrace,
  contract: normalContract,
  outputText: '',
  ...provenance,
});
assert.strictEqual(normal.result.result, 'no-violation');
assert.strictEqual(normal.result.violations.length, 0);
assert.strictEqual(normal.violationReport.observedTraceOnly, true);

const violation = validateRtlolaResults({
  specText: EXPECTED_SPEC,
  traceText: violationTrace,
  contract: violationContract,
  outputText: violationOutput,
  ...provenance,
});
assert.strictEqual(violation.result.result, 'expected-violation');
assert.strictEqual(violation.result.violations.length, 1);
assert.strictEqual(violation.result.violations[0].time, '1.000000000');

expectFailure(
  () => validateSpec(EXPECTED_SPEC.replace('sensitive_operation &&', 'sensitive_operation ||')),
  /allowlisted property/,
);
expectFailure(
  () => parseTrace(normalTrace.replace('false,true,2.0', 'false,true,1.0')),
  /strictly increasing/,
);
expectFailure(
  () => parseTrace(normalTrace.replace('true,false,1.0', 'true,true,1.0')),
  /combines authentication/,
);
expectFailure(
  () => parseTrace(normalTrace.replace('false,true,2.0', 'false,2.0')),
  /missing or adds/,
);
expectFailure(
  () => parseTrace(normalTrace.replace('false,false,0.0', '"false",false,0.0')),
  /quoted/,
);
const dishonestContract = JSON.parse(JSON.stringify(violationContract));
dishonestContract.expectedViolations = [];
expectFailure(
  () => validateRtlolaResults({
    specText: EXPECTED_SPEC,
    traceText: violationTrace,
    contract: dishonestContract,
    outputText: '',
    ...provenance,
  }),
  /expected violation contract/,
);
expectFailure(
  () => parseRtlolaOutput('{"time":"1.000000000","trigger_0":[],"extra":true}\n'),
  /unexpected fields/,
);
expectFailure(
  () => parseRtlolaOutput('x'.repeat(MAX_OUTPUT_BYTES + 1)),
  /64 KiB/,
);
expectFailure(
  () => validateRtlolaResults({
    specText: EXPECTED_SPEC,
    traceText: normalTrace,
    contract: normalContract,
    outputText: violationOutput,
    ...provenance,
  }),
  /RTLola verdicts do not match/,
);

console.log('RTLola result tests passed (finite trace, schema/order, normal/violation, output envelope, and provenance).');
