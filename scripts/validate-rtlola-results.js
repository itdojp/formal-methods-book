#!/usr/bin/env node
'use strict';

const crypto = require('crypto');
const fs = require('fs');

const PROPERTY_ID = 'auth-before-sensitive-operation';
const VIOLATION_MESSAGE = 'AUTH_BEFORE_SENSITIVE violated';
const MAX_SPEC_BYTES = 64 * 1024;
const MAX_TRACE_BYTES = 1024 * 1024;
const MAX_OUTPUT_BYTES = 64 * 1024;
const MAX_TRACE_ROWS = 1000;
const EXPECTED_COLUMNS = ['auth_success', 'sensitive_operation', 'time'];
const EXPECTED_SPEC = [
  'input auth_success: Bool',
  'input sensitive_operation: Bool',
  'input time: Float64',
  '',
  'output authenticated: Bool := auth_success || authenticated.offset(by: -1).defaults(to: false)',
  'trigger sensitive_operation && !authenticated "AUTH_BEFORE_SENSITIVE violated"',
  '',
].join('\n');
const EXPECTED_EVENT_SCHEMA = {
  columns: EXPECTED_COLUMNS,
  timestampColumn: 'time',
  timestampMode: 'relative-float-secs',
  ordering: 'strictly-increasing',
  duplicates: 'rejected',
  missingEvents: 'not-detectable-without-an-external-heartbeat',
  sampling: 'complete-fixed-teaching-trace',
  clockSkew: 'not-applicable-to-one-relative-clock',
};

function sha256(text) {
  return crypto.createHash('sha256').update(text, 'utf8').digest('hex');
}

function assertPlainObject(value, label) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error(label + ' must be an object');
  }
}

function exactKeys(value, expected, label) {
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
    throw new Error(label + ' has unexpected fields: ' + actual.join(', '));
  }
}

function readBoundedText(filePath, maxBytes, label) {
  const stat = fs.statSync(filePath);
  if (!stat.isFile() || stat.size > maxBytes) {
    throw new Error(label + ' must be a regular file no larger than ' + maxBytes + ' bytes');
  }
  const value = fs.readFileSync(filePath, 'utf8');
  if (value.includes('\0')) throw new Error(label + ' contains a NUL byte');
  return value.replaceAll('\r\n', '\n');
}

function validateSpec(text) {
  if (Buffer.byteLength(text, 'utf8') > MAX_SPEC_BYTES) throw new Error('RTLola specification is too large');
  if (text !== EXPECTED_SPEC) {
    throw new Error('RTLola teaching specification does not match the allowlisted property');
  }
  return { propertyId: PROPERTY_ID, violationMessage: VIOLATION_MESSAGE };
}

function parseBoolean(value, row, field) {
  if (value === 'true') return true;
  if (value === 'false') return false;
  throw new Error('trace row ' + row + ' has invalid ' + field + ': ' + value);
}

function parseTrace(text) {
  if (Buffer.byteLength(text, 'utf8') > MAX_TRACE_BYTES) throw new Error('RTLola trace is too large');
  if (/["\r]/.test(text)) throw new Error('teaching trace does not permit quoted or CR-delimited CSV fields');
  const lines = text.trimEnd().split('\n');
  if (lines.length < 2) throw new Error('trace must contain a header and at least one event');
  if (lines[0] !== EXPECTED_COLUMNS.join(',')) throw new Error('trace header does not match the event schema');
  if (lines.length - 1 > MAX_TRACE_ROWS) throw new Error('trace exceeds ' + MAX_TRACE_ROWS + ' event rows');

  const rows = [];
  let previousTimestamp = -Infinity;
  for (let index = 1; index < lines.length; index += 1) {
    const rowNumber = index + 1;
    const values = lines[index].split(',');
    if (values.length !== EXPECTED_COLUMNS.length || values.some((value) => value === '')) {
      throw new Error('trace row ' + rowNumber + ' is missing or adds an event field');
    }
    const authSuccess = parseBoolean(values[0], rowNumber, 'auth_success');
    const sensitiveOperation = parseBoolean(values[1], rowNumber, 'sensitive_operation');
    if (authSuccess && sensitiveOperation) {
      throw new Error('trace row ' + rowNumber + ' combines authentication and a sensitive operation');
    }
    if (!/^(?:0|[1-9]\d*)(?:\.\d+)?$/.test(values[2])) {
      throw new Error('trace row ' + rowNumber + ' has an invalid relative timestamp: ' + values[2]);
    }
    const timestamp = Number(values[2]);
    if (!Number.isFinite(timestamp) || timestamp <= previousTimestamp) {
      throw new Error('trace timestamps must be finite and strictly increasing at row ' + rowNumber);
    }
    previousTimestamp = timestamp;
    rows.push({
      authSuccess,
      sensitiveOperation,
      timestamp,
      rtlolaTime: timestamp.toFixed(9),
    });
  }
  return rows;
}

function deriveViolations(rows) {
  let authenticated = false;
  const violations = [];
  for (const row of rows) {
    authenticated = row.authSuccess || authenticated;
    if (row.sensitiveOperation && !authenticated) {
      violations.push({ time: row.rtlolaTime, message: VIOLATION_MESSAGE });
    }
  }
  return violations;
}

function parseContract(value) {
  assertPlainObject(value, 'expected result contract');
  exactKeys(
    value,
    ['schemaVersion', 'propertyId', 'traceRole', 'expectedResult', 'eventSchema', 'expectedViolations'],
    'expected result contract',
  );
  if (value.schemaVersion !== 1 || value.propertyId !== PROPERTY_ID) {
    throw new Error('expected result contract identity is invalid');
  }
  if (!['normal', 'violation'].includes(value.traceRole)) throw new Error('traceRole must be normal or violation');
  if (!['no-violation', 'expected-violation'].includes(value.expectedResult)) {
    throw new Error('expectedResult must be no-violation or expected-violation');
  }
  if ((value.traceRole === 'normal') !== (value.expectedResult === 'no-violation')) {
    throw new Error('traceRole and expectedResult disagree');
  }
  if (JSON.stringify(value.eventSchema) !== JSON.stringify(EXPECTED_EVENT_SCHEMA)) {
    throw new Error('event schema assumptions do not match the fixed teaching contract');
  }
  if (!Array.isArray(value.expectedViolations)) throw new Error('expectedViolations must be an array');
  for (const [index, item] of value.expectedViolations.entries()) {
    assertPlainObject(item, 'expectedViolations[' + index + ']');
    exactKeys(item, ['time', 'message'], 'expectedViolations[' + index + ']');
    if (!/^\d+\.\d{9}$/.test(item.time) || item.message !== VIOLATION_MESSAGE) {
      throw new Error('expectedViolations[' + index + '] is invalid');
    }
  }
  return value;
}

function parseRtlolaOutput(text) {
  if (Buffer.byteLength(text, 'utf8') > MAX_OUTPUT_BYTES) throw new Error('RTLola output exceeds the 64 KiB contract');
  const lines = text.split(/\r?\n/).filter((line) => line.length > 0);
  return lines.map((line, index) => {
    let value;
    try {
      value = JSON.parse(line);
    } catch (error) {
      throw new Error('RTLola output line ' + (index + 1) + ' is not JSON: ' + error.message);
    }
    assertPlainObject(value, 'RTLola output line ' + (index + 1));
    exactKeys(value, ['time', 'trigger_0'], 'RTLola output line ' + (index + 1));
    if (!/^\d+\.\d{9}$/.test(value.time)) throw new Error('RTLola output line ' + (index + 1) + ' has invalid time');
    if (!Array.isArray(value.trigger_0) || value.trigger_0.length !== 1) {
      throw new Error('RTLola output line ' + (index + 1) + ' must contain exactly one trigger verdict');
    }
    const verdict = value.trigger_0[0];
    assertPlainObject(verdict, 'RTLola output line ' + (index + 1) + ' verdict');
    exactKeys(verdict, ['eval'], 'RTLola output line ' + (index + 1) + ' verdict');
    if (verdict.eval !== VIOLATION_MESSAGE) throw new Error('RTLola output line ' + (index + 1) + ' has an unknown verdict');
    return { time: value.time, message: verdict.eval };
  });
}

function validateRtlolaResults(options) {
  const {
    specText,
    traceText,
    contract,
    outputText,
    toolVersion,
    toolCommit,
    rustToolchain,
    timeLimitSeconds,
  } = options;
  validateSpec(specText);
  const parsedContract = parseContract(contract);
  const rows = parseTrace(traceText);
  const derivedViolations = deriveViolations(rows);
  if (JSON.stringify(parsedContract.expectedViolations) !== JSON.stringify(derivedViolations)) {
    throw new Error('expected violation contract does not match the trace semantics');
  }
  const actualViolations = parseRtlolaOutput(outputText);
  if (JSON.stringify(actualViolations) !== JSON.stringify(derivedViolations)) {
    throw new Error('RTLola verdicts do not match the independently derived trace result');
  }
  if (parsedContract.expectedResult === 'no-violation' && actualViolations.length !== 0) {
    throw new Error('normal trace unexpectedly contains a violation');
  }
  if (parsedContract.expectedResult === 'expected-violation' && actualViolations.length === 0) {
    throw new Error('violation trace did not produce a violation report');
  }
  if (!/^\d+\.\d+\.\d+$/.test(toolVersion)
      || !/^[0-9a-f]{40}$/.test(toolCommit)
      || !/^\d+\.\d+\.\d+$/.test(rustToolchain)
      || !Number.isSafeInteger(timeLimitSeconds)
      || timeLimitSeconds < 1
      || timeLimitSeconds > 900) {
    throw new Error('tool provenance or time limit is invalid');
  }

  const result = {
    schemaVersion: 1,
    result: parsedContract.expectedResult,
    propertyId: parsedContract.propertyId,
    finiteTraceSemantics: 'observed finite prefix only; no claim about unobserved executions',
    tool: {
      name: 'RTLola CLI',
      version: toolVersion,
      commit: toolCommit,
      rustToolchain,
    },
    monitor: {
      mode: 'offline',
      input: 'csv',
      timestampMode: parsedContract.eventSchema.timestampMode,
      output: 'json',
      timeLimitSeconds,
    },
    eventSchema: parsedContract.eventSchema,
    trace: {
      role: parsedContract.traceRole,
      rows: rows.length,
      firstTimestamp: rows[0].rtlolaTime,
      lastTimestamp: rows.at(-1).rtlolaTime,
      sha256: sha256(traceText),
    },
    specification: {
      sha256: sha256(specText),
    },
    violations: actualViolations,
  };
  const violationReport = {
    schemaVersion: 1,
    propertyId: parsedContract.propertyId,
    result: parsedContract.expectedResult,
    observedTraceOnly: true,
    violations: actualViolations,
  };
  const summary = [
    'RTLola CLI ' + toolVersion + ' (' + toolCommit + ')',
    'Rust ' + rustToolchain + '; offline relative CSV; ' + rows.length + ' events',
    'property: ' + parsedContract.propertyId,
    'violations: ' + actualViolations.length,
    'result: ' + parsedContract.expectedResult,
    '',
  ].join('\n');
  return { result, violationReport, summary };
}

function main(argv) {
  if (argv.length !== 11) {
    throw new Error(
      'Usage: validate-rtlola-results.js <raw-output> <spec> <trace> <contract> '
      + '<results.json> <violation-report.json> <summary.log> <version> <commit> <rust-toolchain> <time-limit>',
    );
  }
  const [
    outputPath,
    specPath,
    tracePath,
    contractPath,
    resultPath,
    violationReportPath,
    summaryPath,
    toolVersion,
    toolCommit,
    rustToolchain,
    timeLimit,
  ] = argv;
  const specText = readBoundedText(specPath, MAX_SPEC_BYTES, 'RTLola specification');
  const traceText = readBoundedText(tracePath, MAX_TRACE_BYTES, 'RTLola trace');
  const outputText = readBoundedText(outputPath, MAX_OUTPUT_BYTES, 'RTLola output');
  const contract = JSON.parse(readBoundedText(contractPath, MAX_SPEC_BYTES, 'RTLola expected contract'));
  const validated = validateRtlolaResults({
    specText,
    traceText,
    contract,
    outputText,
    toolVersion,
    toolCommit,
    rustToolchain,
    timeLimitSeconds: Number(timeLimit),
  });
  fs.writeFileSync(resultPath, JSON.stringify(validated.result, null, 2) + '\n');
  fs.writeFileSync(violationReportPath, JSON.stringify(validated.violationReport, null, 2) + '\n');
  fs.writeFileSync(summaryPath, validated.summary);
}

if (require.main === module) {
  try {
    main(process.argv.slice(2));
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}

module.exports = {
  EXPECTED_EVENT_SCHEMA,
  EXPECTED_SPEC,
  MAX_OUTPUT_BYTES,
  deriveViolations,
  parseContract,
  parseRtlolaOutput,
  parseTrace,
  validateRtlolaResults,
  validateSpec,
};
