#!/usr/bin/env node

const { spawnSync } = require('child_process');
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

console.log(`Tool CLI argument tests passed (${cases.length} cases).`);
