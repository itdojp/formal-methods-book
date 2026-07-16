#!/usr/bin/env node

const { spawnSync } = require('child_process');
const fs = require('fs');
const path = require('path');
const { loadToolManifest, validateToolManifest } = require('./tool-manifest');

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
    command: 'tools/sby-check.sh',
    args: ['--config'],
    expected: 'Missing value for --config',
  },
  {
    command: 'tools/sby-check.sh',
    args: ['--task', 'invalid'],
    expected: 'Missing or invalid value for --task',
  },
  {
    command: 'tools/sby-check.sh',
    args: ['--time-limit', '901'],
    expected: 'Missing or invalid value for --time-limit',
  },
  {
    command: 'tools/sby-check.sh',
    args: ['--out-dir', '../../outside', '--config', 'examples/ch08/sby/rtl-arbiter/arbiter-flawed.sby', '--task', 'bmc', 'examples/ch08/sby/rtl-arbiter/arbiter-flawed.sv', 'examples/ch08/sby/rtl-arbiter/expected-flawed-bmc.json'],
    expected: 'SBY --out-dir must be under the repository .artifacts directory',
  },
  {
    command: 'tools/cvc5-proof-check.sh',
    args: ['--out-dir'],
    expected: 'Missing value for --out-dir',
  },
  {
    command: 'tools/cvc5-proof-check.sh',
    args: ['--time-limit', '0'],
    expected: 'Missing or invalid value for --time-limit',
  },
  {
    command: 'tools/cvc5-proof-check.sh',
    args: ['--out-dir', '../../outside', 'examples/proof-certificates/qf-uf-bool-contradiction.smt2'],
    expected: 'cvc5 --out-dir must be under the repository .artifacts directory',
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

const sbyFixtureParent = path.join(repoRoot, 'tools', '.tmp');
fs.mkdirSync(sbyFixtureParent, { recursive: true });
const sbyFixture = fs.mkdtempSync(path.join(sbyFixtureParent, 'sby-cli-test-'));
try {
  const source = path.join(sbyFixture, 'arbiter.sv');
  const config = path.join(sbyFixture, 'malicious.sby');
  const expected = path.join(sbyFixture, 'expected.json');
  fs.writeFileSync(source, 'module arbiter; endmodule\n');
  fs.copyFileSync(path.join(repoRoot, 'examples/ch08/sby/rtl-arbiter/expected-flawed-bmc.json'), expected);
  fs.writeFileSync(config, [
    '[tasks]',
    'bmc',
    '',
    '[options]',
    'bmc: mode bmc',
    'bmc: depth 6',
    '',
    '[engines]',
    'bmc: smtbmc bitwuzla',
    '',
    '[script]',
    'read -formal -sv arbiter.sv',
    'prep -top arbiter',
    '! touch should-not-run',
    '',
    '[files]',
    'arbiter.sv',
    '',
  ].join('\n'));
  const result = spawnSync('bash', [
    'tools/sby-check.sh',
    '--config', path.relative(repoRoot, config),
    '--task', 'bmc',
    path.relative(repoRoot, source),
    path.relative(repoRoot, expected),
  ], { cwd: repoRoot, encoding: 'utf8' });
  const output = `${result.stdout || ''}${result.stderr || ''}`;
  if (result.status !== 2 || !output.includes('SBY [script] does not match the allowlisted teaching profile')) {
    throw new Error(`SBY shell escape was not rejected before bootstrap:\n${output}`);
  }
  if (fs.existsSync(path.join(repoRoot, 'should-not-run'))) {
    fs.rmSync(path.join(repoRoot, 'should-not-run'), { force: true });
    throw new Error('SBY shell escape fixture unexpectedly executed');
  }
} finally {
  fs.rmSync(sbyFixture, { recursive: true, force: true });
}

const sharedOutput = path.join(repoRoot, '.artifacts', 'tests', 'cvc5-shared-output');
const unrelatedOutput = path.join(sharedOutput, 'unrelated.txt');
try {
  fs.mkdirSync(sharedOutput, { recursive: true });
  fs.writeFileSync(unrelatedOutput, 'preserve me\n');
  const result = spawnSync('bash', [
    'tools/cvc5-proof-check.sh',
    '--out-dir', path.relative(repoRoot, sharedOutput),
    'examples/proof-certificates/qf-uf-bool-contradiction.smt2',
  ], { cwd: repoRoot, encoding: 'utf8' });
  const output = `${result.stdout || ''}${result.stderr || ''}`;
  if (result.status !== 2 || !output.includes('must be empty or contain only prior cvc5 outputs')) {
    throw new Error(`shared cvc5 output directory was not rejected before bootstrap:\n${output}`);
  }
  if (fs.readFileSync(unrelatedOutput, 'utf8') !== 'preserve me\n') {
    throw new Error('cvc5 wrapper modified an unrelated artifact');
  }
} finally {
  fs.rmSync(sharedOutput, { recursive: true, force: true });
}

const { manifest: validToolManifest } = loadToolManifest(repoRoot);
for (const field of ['rustToolchain', 'rustToolchainManifest']) {
  const fixture = JSON.parse(JSON.stringify(validToolManifest));
  const cvc5 = fixture.tools.find((tool) => tool.id === 'cvc5');
  delete cvc5[field];
  const errors = validateToolManifest(fixture, { rootDir: repoRoot, checkFiles: false });
  if (!errors.some((error) => error.message.includes(`checker provenance fields require ${field}`))) {
    throw new Error(`cvc5 checker manifest accepted missing ${field}`);
  }
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

console.log(`Tool CLI argument tests passed (${cases.length} negative cases + output-dir/manifest/credential/SBY-config/bulk/standalone helpers).`);
