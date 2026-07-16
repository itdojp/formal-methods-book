#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const YAML = require('yaml');

const REPO_ROOT = path.resolve(__dirname, '..');
const MANUAL_IF = "github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'";

function workflowErrors(content) {
  const errors = [];
  let workflow;
  try {
    workflow = YAML.parse(content);
  } catch (error) {
    return [`workflow YAML を解析できません: ${error.message}`];
  }
  const events = workflow?.on;
  if (!events?.pull_request || !events?.schedule || !events?.workflow_dispatch) {
    errors.push('pull_request / schedule / workflow_dispatch trigger をすべて維持してください');
  }
  const inputs = events?.workflow_dispatch?.inputs;
  if (inputs?.lane?.type !== 'choice' || inputs?.tool?.type !== 'string') {
    errors.push('workflow_dispatch は lane choice と tool string を明示してください');
  }
  const laneOptions = inputs?.lane?.options || [];
  for (const lane of ['nightly', 'optional', 'pr-quick']) {
    if (!laneOptions.includes(lane)) errors.push(`workflow_dispatch lane option がありません: ${lane}`);
  }
  if (!workflow.permissions || Object.keys(workflow.permissions).length !== 1 || workflow.permissions.contents !== 'read') {
    errors.push('workflow permissions は contents: read だけに限定してください');
  }

  const jobs = workflow.jobs || {};
  const quick = jobs['pr-quick'];
  const plan = jobs['matrix-plan'];
  const matrix = jobs['tool-matrix'];
  if (!quick) errors.push('pr-quick job がありません');
  if (!plan) errors.push('matrix-plan job がありません');
  if (!matrix) errors.push('tool-matrix job がありません');

  const runs = (job) => (job?.steps || []).map((step) => step.run).filter((value) => typeof value === 'string');
  const actionStep = (job, action) => (job?.steps || []).find(
    (step) => typeof step.uses === 'string' && step.uses.startsWith(`${action}@`),
  );
  function requireJava17(job, jobName) {
    const step = actionStep(job, 'actions/setup-java');
    if (!step || step.with?.distribution !== 'temurin' || String(step.with?.['java-version']) !== '17') {
      errors.push(`${jobName} job の Java は Temurin 17 にしてください`);
    }
  }
  function requireArtifact(job, jobName) {
    const step = actionStep(job, 'actions/upload-artifact');
    if (!step || step.with?.path !== '.artifacts/manifest') {
      errors.push(`${jobName} artifact path は .artifacts/manifest にしてください`);
      return;
    }
    if (step.if !== 'always()' || step.with?.['include-hidden-files'] !== true) {
      errors.push(`${jobName} artifact は成否にかかわらずhidden filesを含めてください`);
    }
    if (Number(step.with?.['retention-days']) !== 14 || step.with?.['if-no-files-found'] !== 'error') {
      errors.push(`${jobName} artifact は retention 14日かつ欠落をerrorにしてください`);
    }
  }
  function requireManifestCache(job, jobName) {
    const step = actionStep(job, 'actions/cache');
    const key = step?.with?.key;
    if (typeof key !== 'string' || !key.includes("tools/tool-manifest.json") || !key.includes("examples/example-manifest.json")) {
      errors.push(`${jobName} cache key は両manifestのhashを含めてください`);
    }
  }

  if (quick) {
    if (quick.if !== "github.event_name == 'pull_request'") errors.push('pr-quick job はpull_requestだけに限定してください');
    const checkout = actionStep(quick, 'actions/checkout');
    if (Number(checkout?.with?.['fetch-depth']) !== 0) errors.push('pr-quick checkout は関連差分用にfetch-depth: 0が必要です');
    requireJava17(quick, 'pr-quick');
    requireManifestCache(quick, 'pr-quick');
    const command = runs(quick).find((value) => value.includes('examples/ci/pr-quick-check.sh'));
    if (!command || !command.includes('"$BASE_SHA"') || !command.includes('"$HEAD_SHA"')) {
      errors.push('pr-quick job はbase/head SHAをcanonical quick runnerへ渡してください');
    }
    requireArtifact(quick, 'pr-quick');
  }

  if (plan) {
    if (plan.if !== MANUAL_IF) errors.push('matrix-plan job はschedule / workflow_dispatchだけに限定してください');
    if (plan.outputs?.matrix !== '${{ steps.plan.outputs.matrix }}') errors.push('matrix-plan output がplan stepと接続されていません');
    const command = runs(plan).find((value) => value.includes('scripts/plan-formal-matrix.js'));
    if (!command || !command.includes('"$GITHUB_OUTPUT"')) errors.push('matrix-plan は検証済みplannerをGITHUB_OUTPUTへ書いてください');
  }

  if (matrix) {
    if (matrix.if !== MANUAL_IF || matrix.needs !== 'matrix-plan') {
      errors.push('tool-matrix job はschedule/manualかつmatrix-plan依存にしてください');
    }
    if (matrix.strategy?.['fail-fast'] !== false) errors.push('tool-matrix strategy.fail-fast は false にしてください');
    if (matrix.strategy?.matrix !== '${{ fromJSON(needs.matrix-plan.outputs.matrix) }}') {
      errors.push('tool-matrix はvalidated plan outputだけをmatrixにしてください');
    }
    if (matrix['runs-on'] !== 'ubuntu-24.04' || Number(matrix['timeout-minutes']) > 60) {
      errors.push('tool-matrix はUbuntu 24.04かつ60分以内にしてください');
    }
    requireJava17(matrix, 'tool-matrix');
    requireManifestCache(matrix, 'tool-matrix');
    const matrixRuns = runs(matrix);
    if (!matrixRuns.includes('bash examples/ci/prepare-tool.sh "${{ matrix.tool }}"')) {
      errors.push('tool-matrix はallowlist済みtool prerequisite scriptを実行してください');
    }
    if (!matrixRuns.includes('bash examples/ci/matrix-tool-check.sh "${{ matrix.tool }}" "${{ matrix.profile }}"')) {
      errors.push('tool-matrix はcanonical isolated runnerを実行してください');
    }
    requireArtifact(matrix, 'tool-matrix');
  }
  return errors;
}

function documentationErrors(rootDir) {
  const required = {
    'README.md': ['tools/tool-manifest.json', 'workflow_dispatch', 'retention'],
    'examples/ci/README.md': ['matrix-plan', 'fail-fast', 'optional'],
    'src/ja/chapters/chapter12.md': ['tool-matrix', 'scripts/plan-formal-matrix.js', 'resource-exhausted'],
    'src/en/chapters/chapter12.md': ['tool-matrix', 'scripts/plan-formal-matrix.js', 'resource-exhausted'],
    'src/ja/appendices/appendix-b.md': ['tools/tool-manifest.json', 'tool-inventory:start', 'Kani 0.67.0'],
    'src/en/appendices/appendix-b.md': ['tools/tool-manifest.json', 'tool-inventory:start', 'Kani 0.67.0'],
    'src/ja/appendices/appendix-e.md': ['tools/tool-manifest.json', 'documentation-only', 'optional/manual'],
    'src/en/appendices/appendix-e.md': ['tools/tool-manifest.json', 'documentation-only', 'optional/manual'],
  };
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
  const validPath = path.join(REPO_ROOT, '.github', 'workflows', 'formal-checks.yml');
  const valid = fs.readFileSync(validPath, 'utf8');
  if (workflowErrors(valid).length !== 0) throw new Error(`current workflow was rejected: ${workflowErrors(valid).join(' | ')}`);
  const mutations = [
    ['fail-fast: false', 'fail-fast: true', 'fail-fast'],
    ['retention-days: 14', 'retention-days: 90', 'retention 14'],
    ['permissions:\n  contents: read', 'permissions:\n  contents: write', 'contents: read'],
    ['fetch-depth: 0', 'fetch-depth: 1', 'fetch-depth'],
    ['scripts/plan-formal-matrix.js', 'scripts/unvalidated-plan.js', 'planner'],
  ];
  for (const [from, to, diagnostic] of mutations) {
    const broken = valid.replace(from, to);
    if (broken === valid || !workflowErrors(broken).some((error) => error.includes(diagnostic))) {
      throw new Error(`workflow mutation was not rejected: ${diagnostic}`);
    }
  }
  console.log('OK: example workflow contract self-tests passed.');
}

function main() {
  if (process.argv.includes('--self-test')) return runSelfTest();
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
    console.log('OK: PR selection, validated matrix, permissions, artifacts, and documentation match.');
    return;
  }
  for (const error of errors) console.error(error);
  process.exitCode = 1;
}

if (require.main === module) main();

module.exports = { documentationErrors, workflowErrors };
