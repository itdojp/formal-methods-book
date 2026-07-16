#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const {
  compareLemmas,
  parseSummary,
  selectAttackGraph,
  validateExpected,
} = require('./validate-tamarin-results');

const expectedFlawed = JSON.parse(fs.readFileSync(
  path.resolve(__dirname, '../examples/tamarin/replay-challenge/expected-flawed.json'),
  'utf8',
));
const summary = `noise\nsummary of summaries:\n\n  Executable (exists-trace): verified (8 steps)\n  Shared_Key_Secrecy (all-traces): verified (2 steps)\n  Response_Authentication (all-traces): verified (6 steps)\n  No_Replay (all-traces): falsified - found trace (10 steps)\n`;

validateExpected(expectedFlawed);
const actual = parseSummary(summary);
compareLemmas(actual, expectedFlawed.lemmas);
assert.strictEqual(actual[3].steps, 10);
assert.strictEqual(
  selectAttackGraph({ graphs: [{ jgLabel: 'trace_Executable' }, { jgLabel: 'trace_No_Replay-example' }] }, 'No_Replay').jgLabel,
  'trace_No_Replay-example',
);
assert.strictEqual(selectAttackGraph({ graphs: [] }, null), null);

assert.throws(
  () => compareLemmas(
    actual.map((lemma, index) => index === 2 ? { ...lemma, name: 'No_Replay' } : lemma),
    expectedFlawed.lemmas,
  ),
  /name mismatch/,
);
assert.throws(
  () => compareLemmas(
    actual.map((lemma, index) => index === 3 ? { ...lemma, status: 'verified' } : lemma),
    expectedFlawed.lemmas,
  ),
  /status mismatch/,
);
assert.throws(() => selectAttackGraph({ graphs: [] }, 'No_Replay'), /exactly one/);
assert.throws(
  () => selectAttackGraph({ graphs: [{ jgLabel: 'x_No_Replay' }, { jgLabel: 'y_No_Replay' }] }, 'No_Replay'),
  /got 2/,
);
assert.throws(
  () => validateExpected({ ...expectedFlawed, attackLemma: 'Response_Authentication' }),
  /single falsified lemma/,
);
assert.throws(() => parseSummary('summary of summaries:\nunknown'), /no recognized lemma/);

const fixtureParent = path.resolve(__dirname, '../tools/.tmp');
fs.mkdirSync(fixtureParent, { recursive: true });
const fixtureDir = fs.mkdtempSync(path.join(fixtureParent, 'tamarin-result-test-'));
try {
  const expectedPath = path.join(fixtureDir, 'expected.json');
  fs.writeFileSync(expectedPath, JSON.stringify(expectedFlawed));
  assert.doesNotThrow(() => validateExpected(JSON.parse(fs.readFileSync(expectedPath, 'utf8'))));
} finally {
  fs.rmSync(fixtureDir, { recursive: true, force: true });
}

console.log('Tamarin result parser tests passed (identity, status, and attack-graph contracts).');
