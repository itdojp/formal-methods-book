#!/usr/bin/env node

const { spawnSync } = require('child_process');
const fs = require('fs');
const path = require('path');

const repoRoot = path.resolve(__dirname, '..');

const cases = [
  {
    command: 'tools/bootstrap.sh',
    args: ['--lane'],
    expected: 'Missing value for --lane',
  },
  {
    command: 'tools/bootstrap.sh',
    args: ['--tool'],
    expected: 'Missing value for --tool',
  },
  {
    command: 'tools/bootstrap.sh',
    args: ['--lane', '--tool', 'alloy'],
    expected: 'Missing value for --lane',
  },
  {
    command: 'tools/spin-check.sh',
    args: ['--out-dir'],
    expected: 'Missing value for --out-dir',
  },
  {
    command: 'tools/spin-check.sh',
    args: ['--claim'],
    expected: 'Missing value for --claim',
  },
  {
    command: 'tools/spin-check.sh',
    args: ['--out-dir', '--claim', 'never', 'examples/ch08/spin/mutex.pml'],
    expected: 'Missing value for --out-dir',
  },
  {
    command: 'tools/quint-check.sh',
    args: ['--seed'],
    expected: 'Missing value for --seed',
  },
  {
    command: 'tools/prism-check.sh',
    args: ['--out-dir'],
    expected: 'Missing value for --out-dir',
  },
  {
    command: 'tools/prism-check.sh',
    args: [
      'examples/prism/retry-communication/retry-communication.pm',
      'examples/prism/retry-communication/retry-communication.props',
    ],
    expected: 'PRISM expected-results contract not found',
  },
  {
    command: 'tools/tamarin-check.sh',
    args: ['--out-dir'],
    expected: 'Missing value for --out-dir',
  },
  {
    command: 'tools/tamarin-check.sh',
    args: ['examples/tamarin/replay-challenge/replay-flawed.spthy'],
    expected: 'Tamarin expected-results contract not found',
  },
  {
    command: 'tools/tamarin-check.sh',
    args: ['--time-limit', '0'],
    expected: 'Missing or invalid value for --time-limit',
  },
  {
    command: 'tools/tamarin-check.sh',
    args: ['--time-limit', '901'],
    expected: 'Missing or invalid value for --time-limit',
  },
  {
    command: 'tools/kani-check.sh',
    args: ['--harness'],
    expected: 'Missing value for --harness',
  },
  {
    command: 'examples/ci/matrix-tool-check.sh',
    args: ['alloy', 'unexpected'],
    expected: 'Invalid matrix profile',
  },
  {
    command: 'examples/ci/prepare-tool.sh',
    args: ['not-a-tool'],
    expected: 'Unsupported matrix tool',
  },
];

for (const testCase of cases) {
  const result = spawnSync('bash', [testCase.command, ...testCase.args], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
  const output = `${result.stdout || ''}${result.stderr || ''}`;
  if (result.error) {
    throw result.error;
  }
  if (result.status !== 2) {
    throw new Error(
      `${testCase.command} ${testCase.args.join(' ')}: expected exit 2, got ${result.status}\n${output}`,
    );
  }
  const requiresUsage = testCase.command.startsWith('tools/');
  if (!output.includes(testCase.expected) || (requiresUsage && !output.includes('Usage:'))) {
    throw new Error(
      `${testCase.command} ${testCase.args.join(' ')}: expected diagnostic and usage\n${output}`,
    );
  }
}

const tamarinFixtureParent = path.join(repoRoot, 'tools', '.tmp');
fs.mkdirSync(tamarinFixtureParent, { recursive: true });
const tamarinFixture = fs.mkdtempSync(path.join(tamarinFixtureParent, 'tamarin-cli-test-'));
try {
  const model = path.join(tamarinFixture, 'credential.spthy');
  const expected = path.join(tamarinFixture, 'expected.json');
  fs.writeFileSync(model, 'theory Credential\nbegin\n// -----BEGIN PRIVATE KEY-----\nend\n');
  fs.writeFileSync(expected, '{}\n');
  const result = spawnSync('bash', ['tools/tamarin-check.sh', model, expected], {
    cwd: repoRoot,
    encoding: 'utf8',
  });
  const output = `${result.stdout || ''}${result.stderr || ''}`;
  if (result.status !== 2 || !output.includes('prohibited credential-like marker')) {
    throw new Error(`Tamarin credential marker was not rejected:\n${output}`);
  }
} finally {
  fs.rmSync(tamarinFixture, { recursive: true, force: true });
}

const bulkFields = spawnSync('node', [
  'scripts/tool-manifest.js',
  'fields',
  'alloy.version',
  'quint.distribution.sha256',
], { cwd: repoRoot, encoding: 'utf8' });
if (bulkFields.status !== 0
    || !/^6\.2\.0\n[0-9a-f]{64}\n$/.test(bulkFields.stdout)
    || bulkFields.stderr !== '') {
  throw new Error(`bulk tool fields failed:\n${bulkFields.stdout}${bulkFields.stderr}`);
}

const standaloneHelper = spawnSync('bash', ['-c', [
  'set -euo pipefail',
  'unset REPO_ROOT',
  'source tools/lib/tool-manifest.sh',
  'tool_manifest_field alloy version',
].join('\n')], { cwd: repoRoot, encoding: 'utf8' });
if (standaloneHelper.status !== 0 || standaloneHelper.stdout.trim() !== '6.2.0') {
  throw new Error(`standalone tool manifest helper failed:\n${standaloneHelper.stdout}${standaloneHelper.stderr}`);
}

console.log(`Tool CLI argument tests passed (${cases.length} negative cases + credential/bulk/standalone helpers).`);
