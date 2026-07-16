#!/usr/bin/env node
'use strict';

const assert = require('assert');
const { validatePrismResults } = require('./validate-prism-results');

const contract = {
  schemaVersion: 1,
  modelType: 'DTMC',
  engine: 'explicit',
  tolerance: 1e-12,
  results: [
    { property: 'P>=0.99 [ F "success" ]', expected: true },
    { property: 'S=? [ "success" ]', expected: 0.992 },
  ],
};

function output(firstProperty = contract.results[0].property) {
  return [
    'PRISM',
    'Version: 4.10.1',
    'Type:        DTMC',
    `Model checking: ${firstProperty}`,
    'Result: true',
    `Model checking: ${contract.results[1].property}`,
    'Result: 0.992',
    '',
  ].join('\n');
}

assert.deepStrictEqual(validatePrismResults(output(), contract, '4.10.1'), [
  { property: contract.results[0].property, expected: true, actual: true },
  { property: contract.results[1].property, expected: 0.992, actual: 0.992 },
]);

assert.throws(
  () => validatePrismResults(output('P=? [ F "success" ]'), contract, '4.10.1'),
  /PRISM property mismatch at index 0/,
  'a semantically different property must fail before result interpretation',
);

const sameValueNumericSwap = output().replace(
  'Model checking: S=? [ "success" ]',
  'Model checking: P=? [ F "success" ]',
);
assert.throws(
  () => validatePrismResults(sameValueNumericSwap, contract, '4.10.1'),
  /PRISM property mismatch at index 1/,
  'a numeric property swap must fail even when both properties evaluate to 0.992',
);

assert.throws(
  () => validatePrismResults(output().replace('Model checking: S=? [ "success" ]\n', ''), contract, '4.10.1'),
  /Expected 2 evaluated PRISM properties, found 1/,
);

assert.throws(
  () => validatePrismResults(output().replace('Version: 4.10.1', 'Version: 4.10.0'), contract, '4.10.1'),
  /version\/model type marker is missing/,
);

console.log('PRISM result contract tests passed (property identity, count, version, and values).');
