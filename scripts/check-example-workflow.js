#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const YAML = require('yaml');

const REPO_ROOT = path.resolve(__dirname, '..');

function workflowErrors(content) {
  const errors = [];
  let workflow;
  try {
    workflow = YAML.parse(content);
  } catch (error) {
    return [`workflow YAML を解析できません: ${error.message}`];
  }
  const events = workflow && workflow.on;
  if (!events || !events.pull_request || !events.schedule || !events.workflow_dispatch) {
    errors.push('pull_request / schedule / workflow_dispatch trigger をすべて維持してください');
  }
  if (!workflow.permissions || workflow.permissions.contents !== 'read') {
    errors.push('workflow permissions.contents は read に限定してください');
  }

  const jobs = workflow.jobs || {};
  const quick = jobs['pr-quick'];
  const nightly = jobs['nightly-deep'];
  if (!quick) errors.push('pr-quick job がありません');
  if (!nightly) errors.push('nightly-deep job がありません');

  function runs(job) {
    return (job?.steps || []).map((step) => step.run).filter((value) => typeof value === 'string');
  }
  function uses(job) {
    return (job?.steps || []).map((step) => step.uses).filter((value) => typeof value === 'string');
  }
  function actionStep(job, action) {
    return (job?.steps || []).find(
      (step) => typeof step.uses === 'string' && step.uses.startsWith(`${action}@`),
    );
  }
  function requireJava17(job, jobName) {
    const step = actionStep(job, 'actions/setup-java');
    if (!step) {
      errors.push(`${jobName} job に setup-java がありません`);
      return;
    }
    if (step.with?.distribution !== 'temurin' || String(step.with?.['java-version']) !== '17') {
      errors.push(`${jobName} job の Java は Temurin 17 にしてください`);
    }
  }
  function artifactSteps(job) {
    return (job?.steps || [])
      .filter((step) => typeof step.uses === 'string' && step.uses.startsWith('actions/upload-artifact@'));
  }
  function requireArtifactUpload(job, jobName, expectedPath) {
    const step = artifactSteps(job).find((candidate) => candidate.with?.path === expectedPath);
    if (!step) {
      errors.push(`${jobName} artifact path は ${expectedPath} にしてください`);
      return;
    }
    if (step.with?.['include-hidden-files'] !== true) {
      errors.push(`${jobName} artifact upload は hidden な .artifacts を明示的に含めてください`);
    }
  }

  if (quick) {
    if (!uses(quick).some((value) => value.startsWith('actions/setup-node@'))) {
      errors.push('pr-quick job に setup-node がありません');
    }
    requireJava17(quick, 'pr-quick');
    if (!runs(quick).includes('bash examples/ci/pr-quick-check.sh')) {
      errors.push('pr-quick job が canonical quick runner を実行していません');
    }
    requireArtifactUpload(quick, 'pr-quick', '.artifacts/manifest');
  }

  if (nightly) {
    if (nightly.if !== "github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'") {
      errors.push('nightly-deep job は schedule / workflow_dispatch のみに限定してください');
    }
    requireJava17(nightly, 'nightly-deep');
    const nightlyRuns = runs(nightly);
    const requiredCommands = [
      'bash tools/alloy-check.sh --repeat 10 examples/alloy/collection.als',
      'bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg --depth 50 --time-limit 300 examples/tla/QueueBounded.tla',
      'bash tools/apalache-check.sh --config examples/apalache/Counter.cfg --length 50 --init Init --next Next --inv Inv examples/apalache/Counter.tla',
      'bash tools/dafny-verify.sh examples/dafny/Abs.dfy',
      'node scripts/run-example-manifest.js --lane nightly',
    ];
    for (const command of requiredCommands) {
      if (!nightlyRuns.includes(command)) errors.push(`nightly-deep command が不足しています: ${command}`);
    }
    const prerequisiteRun = nightlyRuns.find((command) => command.includes('sudo apt-get install --yes'));
    const prerequisiteMarkers = [
      'sudo apt-get update',
      'bison',
      'build-essential',
      'flex',
      'g++',
      'gcc',
      'm4',
      'patch',
      'pkg-config',
      'python3',
      'python3-venv',
      'xz-utils',
      'python3 -m venv tools/.tmp/nusmv-build-tools',
      'tools/.tmp/nusmv-build-tools/bin/pip install',
      '--require-hashes',
      '--requirement tools/nusmv-build-requirements.txt',
      '$GITHUB_WORKSPACE/tools/.tmp/nusmv-build-tools/bin',
      '$GITHUB_PATH',
    ];
    if (!prerequisiteRun) {
      errors.push('nightly-deep job に source-build prerequisites の導入手順がありません');
    } else {
      for (const marker of prerequisiteMarkers) {
        if (!prerequisiteRun.includes(marker)) {
          errors.push(`nightly-deep prerequisite が不足しています: ${marker}`);
        }
      }
    }
    const cacheStep = actionStep(nightly, 'actions/cache');
    const cacheKey = cacheStep?.with?.key;
    if (typeof cacheKey !== 'string' || !cacheKey.includes("tools/nusmv-build-requirements.txt")) {
      errors.push('nightly-deep cache key に NuSMV build requirements の hash がありません');
    }
    requireArtifactUpload(nightly, 'nightly-deep', '.artifacts');
  }
  return errors;
}

function documentationErrors(rootDir) {
  const required = {
    'README.md': [
      'node scripts/run-example-manifest.js --lane nightly',
      'tools/nusmv-build-requirements.txt',
    ],
    'examples/ci/README.md': ['nightly-deep', 'Ubuntu 24.04 x86-64'],
    'docs/chapters/chapter12/index.md': [
      'actions/setup-node@v6',
      'actions/setup-java@v5',
      'Run pr-quick manifest lane',
      'nightly-deep',
      'node scripts/run-example-manifest.js --lane nightly',
    ],
  };
  for (const locale of ['ja', 'en']) {
    for (const prefix of ['src', 'docs']) {
      const file = prefix === 'src'
        ? `${prefix}/${locale}/appendices/appendix-b.md`
        : `${prefix}/${locale === 'ja' ? '' : 'en/'}appendices/appendix-b/index.md`;
      required[file] = [
        'node scripts/run-example-manifest.js --lane nightly',
        'tools/nusmv-build-requirements.txt',
        'Ubuntu 24.04 x86-64',
      ];
    }
  }

  const errors = [];
  for (const [file, markers] of Object.entries(required)) {
    const absolutePath = path.join(rootDir, file);
    if (!fs.existsSync(absolutePath)) {
      errors.push(`${file}: documentation file がありません`);
      continue;
    }
    const content = fs.readFileSync(absolutePath, 'utf8');
    for (const marker of markers) {
      if (!content.includes(marker)) errors.push(`${file}: workflow marker がありません: ${marker}`);
    }
  }
  return errors;
}

function runSelfTest() {
  const valid = `
on:
  pull_request: {}
  schedule: [{cron: "0 2 * * *"}]
  workflow_dispatch: {}
permissions: {contents: read}
jobs:
  pr-quick:
    steps:
      - uses: actions/setup-node@v6
      - uses: actions/setup-java@v5
        with: {distribution: temurin, java-version: '17'}
      - run: bash examples/ci/pr-quick-check.sh
      - uses: actions/upload-artifact@v7
        with: {path: .artifacts/manifest, include-hidden-files: true}
  nightly-deep:
    if: github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'
    steps:
      - uses: actions/setup-java@v5
        with: {distribution: temurin, java-version: '17'}
      - run: |
          sudo apt-get update
          sudo apt-get install --yes bison build-essential flex g++ gcc m4 patch pkg-config python3 python3-venv xz-utils
          python3 -m venv tools/.tmp/nusmv-build-tools
          tools/.tmp/nusmv-build-tools/bin/pip install --require-hashes --requirement tools/nusmv-build-requirements.txt
          echo "$GITHUB_WORKSPACE/tools/.tmp/nusmv-build-tools/bin" >> "$GITHUB_PATH"
      - uses: actions/cache@v5
        with:
          key: formal-tools-nightly-\${{ hashFiles('tools/nusmv-build-requirements.txt') }}
      - run: bash tools/alloy-check.sh --repeat 10 examples/alloy/collection.als
      - run: bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg --depth 50 --time-limit 300 examples/tla/QueueBounded.tla
      - run: bash tools/apalache-check.sh --config examples/apalache/Counter.cfg --length 50 --init Init --next Next --inv Inv examples/apalache/Counter.tla
      - run: bash tools/dafny-verify.sh examples/dafny/Abs.dfy
      - run: node scripts/run-example-manifest.js --lane nightly
      - uses: actions/upload-artifact@v7
        with: {path: .artifacts, include-hidden-files: true}
`;
  if (workflowErrors(valid).length !== 0) throw new Error('valid workflow fixture was rejected');
  const broken = valid.replace('node scripts/run-example-manifest.js --lane nightly', 'echo skipped');
  if (!workflowErrors(broken).some((error) => error.includes('nightly-deep command'))) {
    throw new Error('missing nightly runner fixture was not rejected');
  }
  const missingQuickJava = valid.replace('      - uses: actions/setup-java@v5\n        with: {distribution: temurin, java-version: \'17\'}\n', '');
  if (!workflowErrors(missingQuickJava).some((error) => error.includes('pr-quick job に setup-java'))) {
    throw new Error('missing pr-quick Java setup fixture was not rejected');
  }
  const missingNightlyPrerequisite = valid.replace('--require-hashes', '--no-compile');
  if (!workflowErrors(missingNightlyPrerequisite).some((error) => error.includes('--require-hashes'))) {
    throw new Error('missing hash-locked nightly prerequisite fixture was not rejected');
  }
  const missingNightlyJava = valid.replace(
    "      - uses: actions/setup-java@v5\n        with: {distribution: temurin, java-version: '17'}\n      - run: |\n",
    '      - run: |\n',
  );
  if (!workflowErrors(missingNightlyJava).some((error) => error.includes('nightly-deep job に setup-java'))) {
    throw new Error('missing nightly Java setup fixture was not rejected');
  }
  const hiddenArtifactsExcluded = valid.replaceAll('include-hidden-files: true', 'include-hidden-files: false');
  if (workflowErrors(hiddenArtifactsExcluded).filter((error) => error.includes('hidden な .artifacts')).length !== 2) {
    throw new Error('hidden artifact exclusion fixture was not rejected for both lanes');
  }
  console.log('OK: example workflow contract self-tests passed.');
}

function main() {
  if (process.argv.includes('--self-test')) {
    runSelfTest();
    return;
  }
  if (process.argv.length > 2) {
    console.error('Usage: node scripts/check-example-workflow.js [--self-test]');
    process.exitCode = 2;
    return;
  }
  const workflowPath = path.join(REPO_ROOT, '.github', 'workflows', 'formal-checks.yml');
  const errors = [
    ...workflowErrors(fs.readFileSync(workflowPath, 'utf8')).map((error) => `.github/workflows/formal-checks.yml: ${error}`),
    ...documentationErrors(REPO_ROOT),
  ];
  if (errors.length === 0) {
    console.log('OK: example workflow jobs, lanes, artifacts, and reader documentation match.');
    return;
  }
  for (const error of errors) console.error(error);
  process.exitCode = 1;
}

main();

module.exports = { documentationErrors, workflowErrors };
