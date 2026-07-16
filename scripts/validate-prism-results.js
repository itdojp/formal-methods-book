#!/usr/bin/env node
'use strict';

const fs = require('fs');

function validateContract(contract) {
  if (!contract
      || contract.schemaVersion !== 1
      || typeof contract.modelType !== 'string'
      || contract.engine !== 'explicit'
      || !Number.isFinite(contract.tolerance)
      || contract.tolerance <= 0
      || contract.tolerance > 1e-6
      || !Array.isArray(contract.results)
      || contract.results.length === 0) {
    throw new Error('Invalid PRISM expected-results contract');
  }
  contract.results.forEach((item, index) => {
    if (!item
        || typeof item.property !== 'string'
        || item.property.length === 0
        || /[\r\n]/.test(item.property)
        || !['boolean', 'number'].includes(typeof item.expected)) {
      throw new Error(`Invalid expected result at index ${index}`);
    }
  });
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function numberFrom(value) {
  const numeric = Number(value.replace(/\s+\(.*\)$/, ''));
  if (!Number.isFinite(numeric)) {
    throw new Error(`Expected numeric PRISM result, got: ${value}`);
  }
  return numeric;
}

function validatePrismResults(text, contract, expectedVersion) {
  validateContract(contract);
  const escapedVersion = escapeRegExp(expectedVersion);
  const escapedModelType = escapeRegExp(contract.modelType);
  if (!new RegExp(`^Version:\\s+${escapedVersion}$`, 'm').test(text)
      || !new RegExp(`^Type:\\s+${escapedModelType}$`, 'm').test(text)) {
    throw new Error('PRISM version/model type marker is missing');
  }

  const evaluatedProperties = Array.from(
    text.matchAll(/^Model checking:\s+([^\r\n]+)$/gm),
    (match) => match[1].trim(),
  );
  const actualResults = Array.from(
    text.matchAll(/^Result:\s+([^\r\n]+)$/gm),
    (match) => match[1].trim(),
  );
  if (evaluatedProperties.length !== contract.results.length) {
    throw new Error(
      `Expected ${contract.results.length} evaluated PRISM properties, found ${evaluatedProperties.length}`,
    );
  }
  if (actualResults.length !== contract.results.length) {
    throw new Error(`Expected ${contract.results.length} PRISM results, found ${actualResults.length}`);
  }

  return contract.results.map((item, index) => {
    if (evaluatedProperties[index] !== item.property) {
      throw new Error(
        `PRISM property mismatch at index ${index}: expected ${item.property}, evaluated ${evaluatedProperties[index]}`,
      );
    }
    let actualValue;
    if (typeof item.expected === 'boolean') {
      if (!/^(?:true|false)$/.test(actualResults[index])) {
        throw new Error(`Expected boolean PRISM result at index ${index}, got: ${actualResults[index]}`);
      }
      actualValue = actualResults[index] === 'true';
      if (actualValue !== item.expected) {
        throw new Error(`Boolean result mismatch for ${item.property}: ${actualValue}`);
      }
    } else {
      actualValue = numberFrom(actualResults[index]);
      if (Math.abs(actualValue - item.expected) > contract.tolerance) {
        throw new Error(`Numeric result mismatch for ${item.property}: ${actualValue}`);
      }
    }
    return { property: item.property, expected: item.expected, actual: actualValue };
  });
}

function main(argv) {
  const [inputPath, outputPath, expectedVersion, contractPath] = argv;
  if (!inputPath || !outputPath || !expectedVersion || !contractPath || argv.length !== 4) {
    throw new Error(
      'Usage: scripts/validate-prism-results.js <prism-output.log> <results.json> <version> <expected-results.json>',
    );
  }
  const text = fs.readFileSync(inputPath, 'utf8');
  const contract = JSON.parse(fs.readFileSync(contractPath, 'utf8'));
  const results = validatePrismResults(text, contract, expectedVersion);
  const report = {
    schemaVersion: 1,
    tool: 'PRISM',
    toolVersion: expectedVersion,
    modelType: contract.modelType,
    engine: contract.engine,
    tolerance: contract.tolerance,
    results,
  };
  fs.writeFileSync(outputPath, `${JSON.stringify(report, null, 2)}\n`, 'utf8');
}

if (require.main === module) {
  main(process.argv.slice(2));
}

module.exports = { validatePrismResults };
