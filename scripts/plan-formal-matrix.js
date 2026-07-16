#!/usr/bin/env node
'use strict';

const path = require('path');
const { loadManifest, validateManifest } = require('./example-manifest');
const { getTool, loadToolManifest } = require('./tool-manifest');

const REPO_ROOT = path.resolve(__dirname, '..');

function planMatrix(toolManifest, exampleManifest, request) {
  const event = request.event;
  const requestedLane = event === 'schedule' ? 'nightly' : request.lane;
  const requestedTool = request.tool || 'all';
  if (!['schedule', 'workflow_dispatch'].includes(event)) throw new Error(`unsupported event: ${event}`);
  if (!['pr-quick', 'nightly', 'optional', 'manual'].includes(requestedLane)) {
    throw new Error(`unsupported executable lane: ${requestedLane}`);
  }
  if (requestedTool !== 'all' && !getTool(toolManifest, requestedTool)) throw new Error(`unknown tool: ${requestedTool}`);

  const rows = [];
  const examplesByTool = new Map();
  for (const entry of exampleManifest.examples) {
    const entries = examplesByTool.get(entry.tool) || [];
    entries.push(entry);
    examplesByTool.set(entry.tool, entries);
  }
  for (const tool of toolManifest.tools) {
    if (requestedTool !== 'all' && requestedTool !== tool.id) continue;
    const entries = examplesByTool.get(tool.id) || [];
    if (requestedLane === 'nightly') {
      if (tool.lane === 'pr-quick' && entries.some((entry) => entry.profiles?.nightly)) {
        rows.push({ tool: tool.id, profile: 'nightly' });
      } else if (tool.lane === 'nightly' && entries.length > 0) {
        rows.push({ tool: tool.id, profile: 'default' });
      }
    } else if (tool.lane === requestedLane && entries.length > 0) {
      rows.push({ tool: tool.id, profile: 'default' });
    }
  }
  if (rows.length === 0) {
    throw new Error(`no executable examples match lane=${requestedLane}, tool=${requestedTool}`);
  }
  return { include: rows };
}

function parseArgs(argv) {
  const result = { event: null, lane: null, tool: 'all' };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--event') result.event = argv[++index] || null;
    else if (arg === '--lane') result.lane = argv[++index] || null;
    else if (arg === '--tool') result.tool = argv[++index] || null;
    else throw new Error(`unknown argument: ${arg}`);
  }
  if (!result.event || !result.lane || !result.tool) throw new Error('--event, --lane, and --tool are required');
  return result;
}

function runSelfTest() {
  const toolManifest = {
    tools: [
      { id: 'quick', lane: 'pr-quick' },
      { id: 'night', lane: 'nightly' },
      { id: 'optional', lane: 'optional' },
      { id: 'docs', lane: 'documentation-only' },
    ],
  };
  const exampleManifest = { examples: [
    { tool: 'quick', profiles: { nightly: {} } },
    { tool: 'night' },
    { tool: 'optional' },
  ] };
  const scheduled = planMatrix(toolManifest, exampleManifest, { event: 'schedule', lane: 'optional', tool: 'all' });
  if (JSON.stringify(scheduled.include) !== JSON.stringify([
    { tool: 'quick', profile: 'nightly' },
    { tool: 'night', profile: 'default' },
  ])) throw new Error('scheduled matrix did not select nightly profiles and tools');
  const optional = planMatrix(toolManifest, exampleManifest, { event: 'workflow_dispatch', lane: 'optional', tool: 'all' });
  if (optional.include.length !== 1 || optional.include[0].tool !== 'optional') throw new Error('optional matrix selection failed');
  let rejected = false;
  try {
    planMatrix(toolManifest, exampleManifest, { event: 'workflow_dispatch', lane: 'optional', tool: 'night' });
  } catch (error) {
    rejected = /no executable examples/.test(error.message);
  }
  if (!rejected) throw new Error('lane/tool mismatch was not rejected');
  console.log('OK: formal matrix planner self-tests passed.');
}

function main() {
  if (process.argv.length === 3 && process.argv[2] === '--self-test') return runSelfTest();
  let request;
  try {
    request = parseArgs(process.argv.slice(2));
    const { manifest: toolManifest } = loadToolManifest(REPO_ROOT);
    const { manifest: exampleManifest, manifestPath: examplePath } = loadManifest(REPO_ROOT);
    const errors = validateManifest(exampleManifest, { rootDir: REPO_ROOT, manifestPath: examplePath, toolManifest });
    if (errors.length > 0) throw new Error(`manifest validation failed: ${errors.map((error) => error.message).join(' | ')}`);
    const matrix = planMatrix(toolManifest, exampleManifest, request);
    process.stdout.write(`matrix=${JSON.stringify(matrix)}\n`);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 2;
  }
}

if (require.main === module) main();

module.exports = { parseArgs, planMatrix };
