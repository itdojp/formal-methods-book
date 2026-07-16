#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');

const MANIFEST_PATH = 'tools/tool-manifest.json';
const EXECUTABLE_LANES = new Set(['pr-quick', 'nightly', 'optional', 'manual']);
const VALID_LANES = new Set([...EXECUTABLE_LANES, 'documentation-only']);
const TOOL_ID_PATTERN = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const SHA256_PATTERN = /^[0-9a-f]{64}$/;

function loadToolManifest(rootDir, manifestPath = MANIFEST_PATH) {
  const absolutePath = path.resolve(rootDir, manifestPath);
  let manifest;
  try {
    manifest = JSON.parse(fs.readFileSync(absolutePath, 'utf8'));
  } catch (error) {
    const wrapped = new Error(`tool manifest を読み込めません: ${manifestPath}: ${error.message}`);
    wrapped.cause = error;
    throw wrapped;
  }
  return { manifest, manifestPath, absolutePath };
}

function validateToolManifest(manifest, options = {}) {
  const rootDir = path.resolve(options.rootDir || process.cwd());
  const manifestPath = options.manifestPath || MANIFEST_PATH;
  const checkFiles = options.checkFiles !== false;
  const errors = [];
  const ids = new Set();
  const aliases = new Map();

  function add(message, id = null) {
    errors.push({
      filePath: manifestPath,
      line: 1,
      message: id ? `[${id}] ${message}` : message,
    });
  }

  if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) {
    add('最上位は object である必要があります');
    return errors;
  }
  if (manifest.schemaVersion !== 1) add('schemaVersion は 1 である必要があります');
  const artifactPolicy = manifest.policy?.artifact;
  for (const field of ['retentionDays', 'maxOutputBytes', 'maxBytesPerExample']) {
    if (!Number.isSafeInteger(artifactPolicy?.[field]) || artifactPolicy[field] <= 0) {
      add(`policy.artifact.${field} は正の safe integer である必要があります`);
    }
  }
  if (!manifest.policy?.updates || !Array.isArray(manifest.policy.updates.procedure)) {
    add('policy.updates.procedure は配列である必要があります');
  }
  const executionPolicy = manifest.policy?.execution;
  const expectedExecutionPolicy = {
    timeout: 'runner-enforced',
    stdoutStderr: 'runner-enforced',
    retainedToolOutput: 'post-run-retention-cap',
    memory: 'declared-budget-only',
  };
  for (const [field, expected] of Object.entries(expectedExecutionPolicy)) {
    if (executionPolicy?.[field] !== expected) add(`policy.execution.${field} は ${expected} である必要があります`);
  }
  if (!Array.isArray(manifest.tools) || manifest.tools.length === 0) {
    add('tools は1件以上の配列である必要があります');
    return errors;
  }

  for (const tool of manifest.tools) {
    const id = tool && typeof tool.id === 'string' ? tool.id : '(unknown)';
    if (!tool || typeof tool !== 'object' || Array.isArray(tool)) {
      add('各 tool は object である必要があります');
      continue;
    }
    if (!TOOL_ID_PATTERN.test(tool.id || '')) add('id は lowercase kebab-case である必要があります', id);
    else if (ids.has(tool.id)) add(`id が重複しています: ${tool.id}`, id);
    else ids.add(tool.id);
    if (typeof tool.name !== 'string' || tool.name.trim() === '') add('name は空でない string である必要があります', id);
    if (!VALID_LANES.has(tool.lane)) {
      add(`lane は ${Array.from(VALID_LANES).join(' / ')} のいずれかである必要があります`, id);
    }
    if (!Array.isArray(tool.aliases) || tool.aliases.length === 0) {
      add('aliases は1件以上の配列である必要があります', id);
    } else {
      const localAliases = new Set();
      for (const alias of tool.aliases) {
        if (typeof alias !== 'string' || alias.trim() === '' || /[\r\n]/.test(alias)) {
          add('alias は改行を含まない空でない string である必要があります', id);
          continue;
        }
        if (localAliases.has(alias)) add(`alias が重複しています: ${alias}`, id);
        localAliases.add(alias);
        const owner = aliases.get(alias);
        if (owner && owner !== tool.id) add(`alias は別 tool と重複できません: ${alias} (${owner})`, id);
        else aliases.set(alias, tool.id);
      }
    }
    for (const locale of ['ja', 'en']) {
      if (typeof tool.reason?.[locale] !== 'string' || tool.reason[locale].trim() === '') {
        add(`reason.${locale} は空でない string である必要があります`, id);
      }
    }
    if (!Array.isArray(tool.platforms) || !Array.isArray(tool.sources)) {
      add('platforms と sources は配列である必要があります', id);
    }
    for (const source of tool.sources || []) {
      if (typeof source !== 'string' || !source.startsWith('https://')) add(`source URL が不正です: ${String(source)}`, id);
    }

    if (EXECUTABLE_LANES.has(tool.lane)) {
      if (typeof tool.version !== 'string' || tool.version.trim() === '') add('executable tool には version が必要です', id);
      if (typeof tool.wrapper !== 'string' || !/^tools\/[a-z0-9-]+\.sh$/.test(tool.wrapper)) {
        add('executable tool の wrapper は tools/*.sh の安全な path にしてください', id);
      } else if (checkFiles && !fs.existsSync(path.join(rootDir, tool.wrapper))) {
        add(`wrapper が存在しません: ${tool.wrapper}`, id);
      }
      if (!tool.distribution || typeof tool.distribution !== 'object') {
        add('executable tool には distribution が必要です', id);
      } else {
        if (typeof tool.distribution.url !== 'string' || !tool.distribution.url.startsWith('https://')) {
          add('distribution.url は https URL である必要があります', id);
        }
        if (!SHA256_PATTERN.test(tool.distribution.sha256 || '')) {
          add('distribution.sha256 は64桁 lowercase hex である必要があります', id);
        }
      }
      if (!Array.isArray(tool.platforms) || tool.platforms.length === 0) {
        add('executable tool には1件以上の platform が必要です', id);
      }
      const hasSbySuiteDependency = [
        tool.suiteVersion,
        tool.suiteCommit,
        tool.yosysVersion,
        tool.yosysCommit,
        tool.bitwuzlaVersion,
        tool.bitwuzlaCommit,
      ].some((value) => value !== undefined);
      if (hasSbySuiteDependency) {
        if (!/^\d{8}$/.test(tool.suiteVersion || '')) add('suiteVersion は YYYYMMDD 形式である必要があります', id);
        for (const field of ['commit', 'suiteCommit', 'yosysCommit', 'bitwuzlaCommit']) {
          if (!/^[0-9a-f]{40}$/.test(tool[field] || '')) add(`${field} は40桁 lowercase hex である必要があります`, id);
        }
        for (const field of ['yosysVersion', 'bitwuzlaVersion']) {
          if (typeof tool[field] !== 'string' || tool[field].trim() === '') add(`${field} は空でない string である必要があります`, id);
        }
      }
      if (tool.rustToolchain !== undefined) {
        if (typeof tool.rustToolchain !== 'string' || tool.rustToolchain.trim() === '') {
          add('rustToolchain は空でない string である必要があります', id);
        }
        if (typeof tool.rustToolchainManifest?.url !== 'string'
            || !tool.rustToolchainManifest.url.startsWith('https://static.rust-lang.org/')) {
          add('rustToolchainManifest.url は static.rust-lang.org の https URL にしてください', id);
        }
        if (!SHA256_PATTERN.test(tool.rustToolchainManifest?.sha256 || '')) {
          add('rustToolchainManifest.sha256 は64桁 lowercase hex である必要があります', id);
        }
      }
      const hasCvc5CheckerDependency = [
        tool.checkerVersion,
        tool.checkerCommit,
        tool.checkerDistribution,
        tool.checkerCargoLockSha256,
        tool.certificateFormat,
        tool.maxCertificateBytes,
        tool.maxCheckerOutputBytes,
        tool.rustcCommit,
        tool.cargoCommit,
        tool.rustHost,
      ].some((value) => value !== undefined);
      if (hasCvc5CheckerDependency) {
        if (tool.id !== 'cvc5') add('checker provenance fields are currently reserved for cvc5', id);
        if (tool.rustToolchain === undefined) {
          add('checker provenance fields require rustToolchain', id);
        }
        if (tool.rustToolchainManifest === undefined) {
          add('checker provenance fields require rustToolchainManifest', id);
        }
        if (typeof tool.checkerVersion !== 'string' || tool.checkerVersion.trim() === '') {
          add('checkerVersion は空でない string である必要があります', id);
        }
        if (!/^[0-9a-f]{40}$/.test(tool.checkerCommit || '')) {
          add('checkerCommit は40桁 lowercase hex である必要があります', id);
        }
        if (typeof tool.checkerDistribution?.url !== 'string' || !tool.checkerDistribution.url.startsWith('https://')) {
          add('checkerDistribution.url は https URL である必要があります', id);
        }
        if (!SHA256_PATTERN.test(tool.checkerDistribution?.sha256 || '')) {
          add('checkerDistribution.sha256 は64桁 lowercase hex である必要があります', id);
        }
        if (!SHA256_PATTERN.test(tool.checkerCargoLockSha256 || '')) {
          add('checkerCargoLockSha256 は64桁 lowercase hex である必要があります', id);
        }
        if (tool.certificateFormat !== 'alethe') add('certificateFormat は alethe である必要があります', id);
        if (!Number.isSafeInteger(tool.maxCertificateBytes) || tool.maxCertificateBytes < 1024 || tool.maxCertificateBytes > 67108864) {
          add('maxCertificateBytes は 1024..67108864 の safe integer である必要があります', id);
        }
        if (!Number.isSafeInteger(tool.maxCheckerOutputBytes) || tool.maxCheckerOutputBytes < 1024 || tool.maxCheckerOutputBytes > 1048576) {
          add('maxCheckerOutputBytes は 1024..1048576 の safe integer である必要があります', id);
        }
        if (!/^[0-9a-f]{40}$/.test(tool.rustcCommit || '')) add('rustcCommit は40桁 lowercase hex である必要があります', id);
        if (!/^[0-9a-f]{40}$/.test(tool.cargoCommit || '')) add('cargoCommit は40桁 lowercase hex である必要があります', id);
        if (tool.rustHost !== 'x86_64-unknown-linux-gnu') add('rustHost は x86_64-unknown-linux-gnu である必要があります', id);
        if (typeof tool.licenses?.solver !== 'string' || typeof tool.licenses?.checker !== 'string') {
          add('licenses.solver / licenses.checker は string である必要があります', id);
        }
      }
      const hasMaudeDependency = [
        tool.maudeVersion,
        tool.maudeCommit,
        tool.maudeDistribution,
      ].some((value) => value !== undefined);
      if (hasMaudeDependency) {
        if (typeof tool.maudeVersion !== 'string' || tool.maudeVersion.trim() === '') {
          add('maudeVersion は空でない string である必要があります', id);
        }
        if (!/^[0-9a-f]{40}$/.test(tool.maudeCommit || '')) {
          add('maudeCommit は40桁 lowercase hex である必要があります', id);
        }
        if (typeof tool.maudeDistribution?.url !== 'string'
            || !tool.maudeDistribution.url.startsWith('https://')) {
          add('maudeDistribution.url は https URL である必要があります', id);
        }
        if (!SHA256_PATTERN.test(tool.maudeDistribution?.sha256 || '')) {
          add('maudeDistribution.sha256 は64桁 lowercase hex である必要があります', id);
        }
      }
    } else if (tool.lane === 'documentation-only') {
      if (tool.version !== null || tool.wrapper !== null || tool.distribution !== null) {
        add('documentation-only tool は version / wrapper / distribution を null にしてください', id);
      }
    }
  }
  return errors;
}

function toolMap(manifest) {
  return new Map((manifest.tools || []).map((tool) => [tool.id, tool]));
}

function getTool(manifest, id) {
  return toolMap(manifest).get(id) || null;
}

function nestedField(object, fieldPath) {
  return fieldPath.split('.').reduce((value, key) => value?.[key], object);
}

function usage(stream = process.stderr) {
  stream.write([
    'Usage:',
    '  node scripts/tool-manifest.js validate',
    '  node scripts/tool-manifest.js field TOOL FIELD',
    '  node scripts/tool-manifest.js fields TOOL.FIELD [TOOL.FIELD ...]',
    '  node scripts/tool-manifest.js tools --lane LANE',
    '  node scripts/tool-manifest.js matrix --lane LANE [--tool all|TOOL]',
    '',
  ].join('\n'));
}

function parseSelectionArgs(argv) {
  let lane = null;
  let tool = 'all';
  for (let index = 0; index < argv.length; index += 1) {
    if (argv[index] === '--lane') {
      lane = argv[index + 1] || null;
      index += 1;
    } else if (argv[index] === '--tool') {
      tool = argv[index + 1] || null;
      index += 1;
    } else {
      throw new Error(`unknown argument: ${argv[index]}`);
    }
  }
  if (!lane) throw new Error('--lane is required');
  if (!VALID_LANES.has(lane) || lane === 'documentation-only') throw new Error(`lane is not executable: ${lane}`);
  if (!tool) throw new Error('--tool value is required');
  return { lane, tool };
}

function main() {
  const rootDir = path.resolve(__dirname, '..');
  let loaded;
  try {
    loaded = loadToolManifest(rootDir);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 2;
    return;
  }
  const errors = validateToolManifest(loaded.manifest, { rootDir, manifestPath: loaded.manifestPath });
  if (errors.length > 0) {
    for (const error of errors) console.error(`::error file=${error.filePath},line=${error.line}::${error.message}`);
    process.exitCode = 2;
    return;
  }

  const [command, ...argv] = process.argv.slice(2);
  try {
    if (command === 'validate') {
      console.log(`OK: ${loaded.manifest.tools.length} tool inventory entries are valid.`);
      return;
    }
    if (command === 'field') {
      if (argv.length !== 2) throw new Error('field requires TOOL and FIELD');
      const tool = getTool(loaded.manifest, argv[0]);
      if (!tool) throw new Error(`unknown tool: ${argv[0]}`);
      const value = nestedField(tool, argv[1]);
      if (value === undefined || value === null || typeof value === 'object') {
        throw new Error(`field is not a scalar: ${argv[0]}.${argv[1]}`);
      }
      process.stdout.write(`${String(value)}\n`);
      return;
    }
    if (command === 'fields') {
      if (argv.length === 0) throw new Error('fields requires at least one TOOL.FIELD selector');
      const values = argv.map((selector) => {
        const separator = selector.indexOf('.');
        if (separator <= 0 || separator === selector.length - 1) {
          throw new Error(`invalid field selector: ${selector}`);
        }
        const toolId = selector.slice(0, separator);
        const fieldPath = selector.slice(separator + 1);
        const tool = getTool(loaded.manifest, toolId);
        if (!tool) throw new Error(`unknown tool: ${toolId}`);
        const value = nestedField(tool, fieldPath);
        if (value === undefined || value === null || typeof value === 'object') {
          throw new Error(`field is not a scalar: ${selector}`);
        }
        const rendered = String(value);
        if (/\r|\n/.test(rendered)) throw new Error(`field contains a newline: ${selector}`);
        return rendered;
      });
      process.stdout.write(`${values.join('\n')}\n`);
      return;
    }
    if (command === 'tools' || command === 'matrix') {
      const selection = parseSelectionArgs(argv);
      let tools = loaded.manifest.tools.filter((tool) => tool.lane === selection.lane);
      if (selection.tool !== 'all') tools = tools.filter((tool) => tool.id === selection.tool);
      if (tools.length === 0) throw new Error(`no executable tool matches lane=${selection.lane}, tool=${selection.tool}`);
      if (command === 'tools') {
        process.stdout.write(`${tools.map((tool) => tool.id).join('\n')}\n`);
      } else {
        process.stdout.write(`${JSON.stringify(tools.map((tool) => ({ tool: tool.id })))}\n`);
      }
      return;
    }
    usage();
    process.exitCode = 2;
  } catch (error) {
    console.error(error.message);
    usage();
    process.exitCode = 2;
  }
}

if (require.main === module) main();

module.exports = {
  EXECUTABLE_LANES,
  MANIFEST_PATH,
  VALID_LANES,
  getTool,
  loadToolManifest,
  nestedField,
  toolMap,
  validateToolManifest,
};
