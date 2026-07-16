#!/usr/bin/env node
'use strict';

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');
const { TOOL_WRAPPERS, loadManifest, parseManifestCommand, validateManifest } = require('./example-manifest');
const { getTool, loadToolManifest } = require('./tool-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');
const GLOBAL_QUICK_PATHS = new Set([
  '.github/workflows/formal-checks.yml',
  'examples/ci/pr-quick-check.sh',
  'examples/example-manifest.json',
  'scripts/example-manifest.js',
  'scripts/run-example-manifest.js',
  'scripts/tool-manifest.js',
  'tools/bootstrap.sh',
  'tools/lib/tool-manifest.sh',
  'tools/tool-manifest.json',
]);

function usage(stream = process.stderr) {
  stream.write([
    'Usage:',
    '  node scripts/run-example-manifest.js --id ID',
    '  node scripts/run-example-manifest.js --tool TOOL [--profile nightly]',
    '  node scripts/run-example-manifest.js --lane pr-quick|nightly|optional|manual [--changed-from REF --changed-to REF]',
    '',
  ].join('\n'));
}

function parseArgs(argv) {
  let id = null;
  let lane = null;
  let tool = null;
  let changedFrom = null;
  let changedTo = 'HEAD';
  let profile = null;
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--id') {
      id = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--lane') {
      lane = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--tool') {
      tool = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--changed-from') {
      changedFrom = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--changed-to') {
      changedTo = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--profile') {
      profile = argv[index + 1] || null;
      index += 1;
    } else if (arg === '--help' || arg === '-h') {
      usage(process.stdout);
      process.exit(0);
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  if ([id, lane, tool].filter((value) => value !== null).length !== 1) {
    throw new Error('specify exactly one of --id, --tool, or --lane');
  }
  if (changedFrom !== null && lane !== 'pr-quick') {
    throw new Error('--changed-from is only valid with --lane pr-quick');
  }
  if (changedFrom === null && changedTo !== 'HEAD') {
    throw new Error('--changed-to requires --changed-from');
  }
  if (profile !== null && (profile !== 'nightly' || tool === null)) {
    throw new Error('--profile nightly is only valid with --tool');
  }
  return { id, lane, tool, changedFrom, changedTo, profile };
}

function writeText(filePath, value) {
  fs.writeFileSync(filePath, value, 'utf8');
}

function sha256(value) {
  return crypto.createHash('sha256').update(value).digest('hex');
}

function hashInputs(repoRoot, entry) {
  const paths = [...entry.assets, ...(entry.config ? [entry.config] : [])].sort();
  const files = paths.map((relativePath) => {
    const bytes = fs.readFileSync(path.join(repoRoot, relativePath));
    return { path: relativePath, sha256: sha256(bytes), bytes: bytes.length };
  });
  const aggregate = files.map((file) => `${file.path}\0${file.sha256}\0${file.bytes}\n`).join('');
  return { algorithm: 'sha256', hash: sha256(aggregate), files };
}

function directorySize(directory) {
  if (!fs.existsSync(directory)) return 0;
  let total = 0;
  for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
    const child = path.join(directory, entry.name);
    if (entry.isDirectory()) total += directorySize(child);
    else if (entry.isFile()) total += fs.statSync(child).size;
  }
  return total;
}

function classifyOutcome(result, stdout, stderr, entry, artifactExceeded) {
  if (artifactExceeded || result.error?.code === 'ENOBUFS') return 'resource-exhausted';
  if (result.error?.code === 'ETIMEDOUT' || result.signal === 'SIGTERM') return 'timeout';
  const combined = `${stdout}\n${stderr}`;
  const exitCode = Number.isInteger(result.status) ? result.status : 1;
  // GNU timeout and coreutils-compatible gtimeout use 124 when the wrapped
  // command reaches its limit. TLC also applies this inner wall-clock bound.
  if (exitCode === 124) return 'timeout';
  if (exitCode === entry.expected.exitCode && stdout.includes(entry.expected.stdoutMarker) && !result.error) {
    return entry.expected.outcome;
  }
  if (/\bunknown\b/i.test(combined)) return 'unknown';
  if (/counterexample|verification failed|is false|errors:\s*[1-9]/i.test(combined)) return 'counterexample';
  return 'tool-error';
}

function runEntry(entry, options = {}) {
  const repoRoot = path.resolve(options.repoRoot || REPO_ROOT);
  const emitOutput = options.emitOutput !== false;
  const profile = options.profile || null;
  const profileDefinition = profile ? entry.profiles?.[profile] : null;
  if (profile && !profileDefinition) throw new Error(`profile ${profile} is not defined for ${entry.id}`);
  const runtimeEntry = profile ? {
    ...entry,
    ...profileDefinition,
    id: `${entry.id}--${profile}`,
    lane: profile,
    expected: profileDefinition.expected || entry.expected,
  } : entry;
  const toolManifest = options.toolManifest || loadToolManifest(repoRoot).manifest;
  const tool = getTool(toolManifest, runtimeEntry.tool);
  if (!tool) throw new Error(`tool manifest entry not found: ${runtimeEntry.tool}`);
  const toolDependencies = Object.fromEntries(
    ['rustToolchain', 'embeddedCbmcVersion', 'maudeVersion', 'maudeCommit']
      .filter((field) => tool[field] !== undefined)
      .map((field) => [field, tool[field]]),
  );
  if (tool.rustToolchainManifest) toolDependencies.rustToolchainManifest = tool.rustToolchainManifest;
  if (tool.maudeDistribution) toolDependencies.maudeDistribution = tool.maudeDistribution;
  const artifactPolicy = toolManifest.policy.artifact;
  const artifactDir = path.join(repoRoot, '.artifacts', 'manifest', runtimeEntry.id);
  fs.rmSync(artifactDir, { recursive: true, force: true });
  fs.mkdirSync(artifactDir, { recursive: true });

  const commandPath = path.join(artifactDir, 'command.txt');
  const stdoutPath = path.join(artifactDir, 'stdout.log');
  const stderrPath = path.join(artifactDir, 'stderr.log');
  const metadataPath = path.join(artifactDir, 'metadata.json');
  writeText(commandPath, `${runtimeEntry.command}\n`);
  writeText(stdoutPath, '');
  writeText(stderrPath, '');

  const input = hashInputs(repoRoot, runtimeEntry);
  const startedAt = new Date();
  const invocation = parseManifestCommand(runtimeEntry);
  const result = spawnSync(invocation.executable, invocation.args, {
    cwd: repoRoot,
    encoding: 'utf8',
    maxBuffer: artifactPolicy.maxOutputBytes,
    timeout: runtimeEntry.limits.timeoutSeconds * 1000,
    killSignal: 'SIGTERM',
  });
  const finishedAt = new Date();
  const stdout = result.stdout || '';
  let stderr = result.stderr || '';
  if (result.error) stderr += `${stderr.endsWith('\n') || stderr.length === 0 ? '' : '\n'}${result.error.message}\n`;
  writeText(stdoutPath, stdout);
  writeText(stderrPath, stderr);

  const toolOutputDir = path.join(artifactDir, 'tool-output');
  const measuredToolOutputBytes = directorySize(toolOutputDir);
  const artifactExceeded = measuredToolOutputBytes > artifactPolicy.maxBytesPerExample;
  if (artifactExceeded) {
    fs.rmSync(toolOutputDir, { recursive: true, force: true });
    writeText(
      path.join(artifactDir, 'tool-output-removed.txt'),
      `Tool output exceeded ${artifactPolicy.maxBytesPerExample} bytes and was removed (measured ${measuredToolOutputBytes}).\n`,
    );
  }

  const exitCode = Number.isInteger(result.status) ? result.status : 1;
  const exitCodeMatches = exitCode === runtimeEntry.expected.exitCode;
  const stdoutMarkerFound = stdout.includes(runtimeEntry.expected.stdoutMarker);
  const outcome = classifyOutcome(result, stdout, stderr, runtimeEntry, artifactExceeded);
  const passed = outcome === runtimeEntry.expected.outcome && exitCodeMatches && stdoutMarkerFound && !result.error;
  const metadata = {
    schemaVersion: 2,
    id: runtimeEntry.id,
    sourceExampleId: entry.id,
    profile,
    tool: runtimeEntry.tool,
    toolVersion: tool.version,
    toolCommit: tool.commit || null,
    toolDependencies,
    chapter: runtimeEntry.chapter,
    anchor: runtimeEntry.anchor,
    lane: runtimeEntry.lane,
    command: runtimeEntry.command,
    input,
    limits: runtimeEntry.limits,
    limitEnforcement: toolManifest.policy.execution,
    artifactPolicy,
    expected: runtimeEntry.expected,
    actual: {
      exitCode,
      signal: result.signal || null,
      errorCode: result.error?.code || null,
      stdoutMarkerFound,
      outcome,
      stdoutBytes: Buffer.byteLength(stdout),
      stderrBytes: Buffer.byteLength(stderr),
      toolOutputBytes: measuredToolOutputBytes,
    },
    result: passed ? 'passed' : 'failed',
    startedAt: startedAt.toISOString(),
    finishedAt: finishedAt.toISOString(),
    durationMs: finishedAt.getTime() - startedAt.getTime(),
  };
  writeText(metadataPath, `${JSON.stringify(metadata, null, 2)}\n`);

  if (emitOutput && stdout) process.stdout.write(stdout);
  if (emitOutput && stderr) process.stderr.write(stderr);
  if (emitOutput && !passed) {
    console.error(
      `::error title=Example ${runtimeEntry.id}::expected ${runtimeEntry.expected.outcome}/exit ${runtimeEntry.expected.exitCode}, got ${outcome}/exit ${exitCode}`,
    );
  }
  if (emitOutput) console.log(`${passed ? 'PASS' : 'FAIL'}: ${runtimeEntry.id} (${tool.name} ${tool.version})`);
  return passed;
}

function gitChangedFiles(repoRoot, fromRef, toRef) {
  const result = spawnSync('git', ['diff', '--name-only', '-z', '--diff-filter=ACMRT', `${fromRef}...${toRef}`], {
    cwd: repoRoot,
    encoding: 'utf8',
    maxBuffer: 8 * 1024 * 1024,
  });
  if (result.status !== 0 || result.error) {
    throw new Error(`git diff failed for ${fromRef}...${toRef}: ${(result.stderr || result.error?.message || '').trim()}`);
  }
  return result.stdout.split('\0').filter(Boolean).sort();
}

function selectRelatedQuickEntries(entries, changedFiles) {
  if (changedFiles.some((file) => GLOBAL_QUICK_PATHS.has(file) || file.startsWith('tools/lib/'))) {
    return { entries, reason: 'shared formal-check infrastructure changed' };
  }
  const selected = entries.filter((entry) => {
    const related = new Set([...entry.assets, ...entry.references, entry.config, TOOL_WRAPPERS[entry.tool]].filter(Boolean));
    return changedFiles.some((file) => related.has(file));
  });
  return { entries: selected, reason: 'selected by manifest assets, references, config, and wrapper paths' };
}

function writeSelectionArtifact(repoRoot, selection, changedFiles, reason) {
  const directory = path.join(repoRoot, '.artifacts', 'manifest');
  fs.mkdirSync(directory, { recursive: true });
  writeText(path.join(directory, 'selection.json'), `${JSON.stringify({
    schemaVersion: 1,
    reason,
    changedFiles,
    selectedIds: selection.map((entry) => entry.id),
  }, null, 2)}\n`);
}

function main() {
  let selection;
  try {
    selection = parseArgs(process.argv.slice(2));
  } catch (error) {
    console.error(error.message);
    usage();
    process.exitCode = 2;
    return;
  }

  const { manifest, manifestPath } = loadManifest(REPO_ROOT);
  const toolManifest = loadToolManifest(REPO_ROOT).manifest;
  const errors = validateManifest(manifest, { rootDir: REPO_ROOT, manifestPath, toolManifest });
  if (errors.length > 0) {
    for (const error of errors) console.error(`::error file=${error.filePath},line=${error.line}::${error.message}`);
    console.error(`Manifest validation failed with ${errors.length} error(s).`);
    process.exitCode = 2;
    return;
  }

  let entries;
  if (selection.id !== null) entries = manifest.examples.filter((entry) => entry.id === selection.id);
  else if (selection.tool !== null) entries = manifest.examples.filter((entry) => entry.tool === selection.tool);
  else entries = manifest.examples.filter((entry) => entry.lane === selection.lane);
  if (entries.length === 0) {
    console.error(`Unknown or empty selector: ${selection.id || selection.tool || selection.lane}`);
    process.exitCode = 2;
    return;
  }
  if (selection.profile) {
    entries = entries.filter((entry) => entry.profiles?.[selection.profile]);
    if (entries.length === 0) {
      console.error(`Tool ${selection.tool} has no ${selection.profile} profile`);
      process.exitCode = 2;
      return;
    }
  }

  let changedFiles = [];
  let reason = 'explicit id/tool/lane selection';
  if (selection.changedFrom !== null) {
    try {
      changedFiles = gitChangedFiles(REPO_ROOT, selection.changedFrom, selection.changedTo);
      ({ entries, reason } = selectRelatedQuickEntries(entries, changedFiles));
    } catch (error) {
      console.error(error.message);
      process.exitCode = 2;
      return;
    }
  }
  writeSelectionArtifact(REPO_ROOT, entries, changedFiles, reason);
  if (entries.length === 0) {
    console.log('SKIP: no related pr-quick examples for this diff');
    return;
  }

  let passed = true;
  for (const entry of entries) {
    if (!runEntry(entry, { toolManifest, profile: selection.profile })) passed = false;
  }
  if (!passed) process.exitCode = 1;
}

if (require.main === module) main();

module.exports = {
  classifyOutcome,
  gitChangedFiles,
  hashInputs,
  parseArgs,
  runEntry,
  selectRelatedQuickEntries,
};
