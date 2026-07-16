#!/usr/bin/env node
'use strict';

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { getTool, loadToolManifest } = require('./tool-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');
const TINY_QF_UF_CONTRADICTION = [
  '(set-logic QF_UF)',
  '(declare-const p Bool)',
  '(assert p)',
  '(assert (not p))',
  '(check-sat)',
  '',
].join('\n');

function sha256(value) {
  return crypto.createHash('sha256').update(value).digest('hex');
}

function readUtf8(filePath, label) {
  const bytes = fs.readFileSync(filePath);
  const text = bytes.toString('utf8');
  if (!Buffer.from(text, 'utf8').equals(bytes)) throw new Error(`${label} is not valid UTF-8`);
  return text;
}

function validateTinySmt2(text) {
  if (text !== TINY_QF_UF_CONTRADICTION) {
    throw new Error('SMT2 input must be the exact self-contained QF_UF Bool contradiction teaching grammar');
  }
  return { logic: 'QF_UF', declaredConstant: 'p', assertions: ['p', '(not p)'] };
}

function balancedAlethe(text) {
  if (!text.startsWith('(') || !text.endsWith(')\n')) {
    throw new Error('Alethe certificate must be one parenthesized expression terminated by one newline');
  }
  let depth = 0;
  let quote = null;
  let escaped = false;
  for (const char of text) {
    if (quote === '"') {
      if (escaped) escaped = false;
      else if (char === '\\') escaped = true;
      else if (char === '"') quote = null;
      continue;
    }
    if (quote === '|') {
      if (char === '|') quote = null;
      continue;
    }
    if (char === '"' || char === '|') {
      quote = char;
    } else if (char === '(') {
      depth += 1;
    } else if (char === ')') {
      depth -= 1;
      if (depth < 0) throw new Error('Alethe certificate has an unmatched closing parenthesis');
    }
  }
  if (quote || depth !== 0) throw new Error('Alethe certificate is not a balanced complete expression');
}

function parseSolverEnvelope(raw, maxCertificateBytes) {
  if (!Number.isSafeInteger(maxCertificateBytes) || maxCertificateBytes < 1024) {
    throw new Error('Invalid maximum certificate size');
  }
  if (raw.includes('\0') || raw.includes('\r') || /[^\x09\x0a\x20-\x7e]/.test(raw)) {
    throw new Error('cvc5 output contains an unsupported control or non-ASCII character');
  }
  const firstNewline = raw.indexOf('\n');
  if (firstNewline < 0) throw new Error('cvc5 output did not contain a solver status line');
  const status = raw.slice(0, firstNewline);
  const rest = raw.slice(firstNewline + 1);
  if (!['sat', 'unsat', 'unknown'].includes(status)) {
    throw new Error(`unexpected cvc5 solver status: ${status || '<empty>'}`);
  }
  if (status !== 'unsat') {
    if (rest !== '') throw new Error(`cvc5 ${status} output must not use an additional output channel`);
    return { status, certificate: null, certificateBytes: 0 };
  }
  if (Buffer.byteLength(rest) > maxCertificateBytes) {
    const error = new Error(`Alethe certificate exceeds ${maxCertificateBytes} bytes`);
    error.code = 'PROOF_TOO_LARGE';
    throw error;
  }
  balancedAlethe(rest);
  return { status, certificate: rest, certificateBytes: Buffer.byteLength(rest) };
}

function classifyChecker(checkerStatus, checkerOutput) {
  if (checkerStatus === 124) return 'checker-timeout';
  if (checkerStatus === 125) return 'checker-output-too-large';
  if (checkerStatus === 0 && checkerOutput === 'valid\n') return 'success';
  if (/\bhole\b/i.test(checkerOutput)) return 'checker-holey';
  if (/\bunknown\b/i.test(checkerOutput)) return 'checker-unknown';
  return 'checker-invalid';
}

function solverResult({ solverStatus, raw, maxCertificateBytes }) {
  if (solverStatus === 124) return { result: 'solver-timeout', envelope: null };
  if (solverStatus !== 0) return { result: 'solver-error', envelope: null };
  try {
    const envelope = parseSolverEnvelope(raw, maxCertificateBytes);
    if (envelope.status === 'sat') return { result: 'solver-sat', envelope };
    if (envelope.status === 'unknown') return { result: 'solver-unknown', envelope };
    return { result: null, envelope };
  } catch (error) {
    return { result: error.code === 'PROOF_TOO_LARGE' ? 'proof-too-large' : 'solver-invalid-output', envelope: null };
  }
}

function writeResults(options) {
  const input = readUtf8(options.inputPath, 'SMT2 input');
  const inputShape = validateTinySmt2(input);
  const raw = readUtf8(options.solverRawPath, 'cvc5 output');
  const { manifest } = loadToolManifest(options.repoRoot || REPO_ROOT);
  const tool = getTool(manifest, 'cvc5');
  if (!tool) throw new Error('cvc5 tool manifest entry was not found');
  const checkerOutputBytes = options.checkerRawPath && fs.existsSync(options.checkerRawPath)
    ? fs.statSync(options.checkerRawPath).size
    : 0;
  const checkerOutputExceeded = checkerOutputBytes >= tool.maxCheckerOutputBytes;
  const checkerOutput = options.checkerRawPath && fs.existsSync(options.checkerRawPath) && !checkerOutputExceeded
    ? readUtf8(options.checkerRawPath, 'Carcara output')
    : '';
  const solver = solverResult({ solverStatus: options.solverStatus, raw, maxCertificateBytes: tool.maxCertificateBytes });
  const checkerStatus = checkerOutputExceeded ? 125 : options.checkerStatus;
  const result = solver.result || classifyChecker(checkerStatus, checkerOutput);
  const certificate = solver.envelope?.certificate || null;
  const report = {
    schemaVersion: 1,
    result,
    input: {
      file: path.basename(options.inputPath),
      sha256: sha256(input),
      grammar: inputShape,
    },
    solver: {
      name: 'cvc5',
      version: tool.version,
      commit: tool.commit,
      distribution: tool.distribution,
    },
    checker: {
      name: 'Carcara',
      version: tool.checkerVersion,
      commit: tool.checkerCommit,
      distribution: tool.checkerDistribution,
      cargoLockSha256: tool.checkerCargoLockSha256,
      maxOutputBytes: tool.maxCheckerOutputBytes,
    },
    rust: {
      toolchain: tool.rustToolchain,
      rustcCommit: tool.rustcCommit,
      cargoCommit: tool.cargoCommit,
      host: tool.rustHost,
      manifest: tool.rustToolchainManifest,
    },
    certificateFormat: tool.certificateFormat,
    commands: {
      solver: ['cvc5', '--lang', 'smt2', '--produce-proofs', '--dump-proofs', '--proof-format-mode=alethe', path.basename(options.inputPath)],
      checker: ['carcara', 'check', 'certificate.alethe', path.basename(options.inputPath)],
    },
    limits: {
      timeoutSeconds: options.timeLimitSeconds,
      maxCertificateBytes: tool.maxCertificateBytes,
      maxCheckerOutputBytes: tool.maxCheckerOutputBytes,
    },
    evidence: {
      solverExitCode: options.solverStatus,
      solverOutputSha256: sha256(raw),
      checkerExitCode: solver.result ? null : checkerStatus,
      checkerOutputBytes,
      checkerOutputSha256: checkerOutput === '' ? null : sha256(checkerOutput),
      certificate: certificate === null ? null : {
        file: 'certificate.alethe',
        bytes: Buffer.byteLength(certificate),
        sha256: sha256(certificate),
      },
    },
  };
  fs.writeFileSync(options.resultsPath, `${JSON.stringify(report, null, 2)}\n`);
  const summary = [
    `cvc5 ${tool.version} (${tool.commit})`,
    `Carcara ${tool.checkerVersion} (${tool.checkerCommit})`,
    `Rust ${tool.rustToolchain}; certificate format ${tool.certificateFormat}`,
    `solver exit: ${options.solverStatus}; checker exit: ${report.evidence.checkerExitCode === null ? 'not-run' : report.evidence.checkerExitCode}`,
    `result: ${result}`,
  ];
  if (report.evidence.certificate) summary.splice(3, 0, `certificate: ${report.evidence.certificate.bytes} bytes; sha256 ${report.evidence.certificate.sha256}`);
  fs.writeFileSync(options.summaryPath, `${summary.join('\n')}\n`);
  return report;
}

function main(argv) {
  const [action, ...args] = argv;
  try {
    if (action === 'extract' && args.length === 3 && /^\d+$/.test(args[2])) {
      const envelope = parseSolverEnvelope(readUtf8(args[0], 'cvc5 output'), Number(args[2]));
      if (envelope.status !== 'unsat' || !envelope.certificate) throw new Error(`cvc5 result is ${envelope.status}, not unsat`);
      fs.writeFileSync(args[1], envelope.certificate, { mode: 0o600 });
      return;
    }
    if (action === 'write' && args.length === 8 && /^-?\d+$/.test(args[3]) && /^-?\d+$/.test(args[4]) && /^[1-9]\d*$/.test(args[7])) {
      writeResults({
        solverRawPath: args[0], inputPath: args[1], checkerRawPath: args[2] || null,
        solverStatus: Number(args[3]), checkerStatus: Number(args[4]), resultsPath: args[5], summaryPath: args[6],
        timeLimitSeconds: Number(args[7]), repoRoot: REPO_ROOT,
      });
      return;
    }
    throw new Error('Usage: validate-cvc5-proof-results.js extract RAW CERT MAX_BYTES | write RAW INPUT CHECKER_RAW SOLVER_STATUS CHECKER_STATUS RESULTS SUMMARY TIME_LIMIT_SECONDS');
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}

if (require.main === module) main(process.argv.slice(2));

module.exports = { TINY_QF_UF_CONTRADICTION, classifyChecker, parseSolverEnvelope, solverResult, validateTinySmt2, writeResults };
