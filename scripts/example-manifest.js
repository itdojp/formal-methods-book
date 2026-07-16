#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const {
  EXECUTABLE_LANES,
  getTool,
  loadToolManifest,
  validateToolManifest,
} = require('./tool-manifest');

const MANIFEST_PATH = 'examples/example-manifest.json';
const VALID_LANES = EXECUTABLE_LANES;
const VALID_OUTCOMES = new Set(['success', 'counterexample']);
const DOCUMENT_PATTERN = /^(?:chapter\d{2}|appendix-[a-z0-9]+(?:-[a-z0-9]+)*)$/;
const TOOL_WRAPPERS = Object.freeze({
  alloy: 'tools/alloy-check.sh',
  tlc: 'tools/tlc-run.sh',
  apalache: 'tools/apalache-check.sh',
  dafny: 'tools/dafny-verify.sh',
  spin: 'tools/spin-check.sh',
  nusmv: 'tools/nusmv-check.sh',
  cbmc: 'tools/cbmc-check.sh',
  quint: 'tools/quint-check.sh',
  prism: 'tools/prism-check.sh',
  tamarin: 'tools/tamarin-check.sh',
  kani: 'tools/kani-check.sh',
});
const TOOL_OPTION_CONTRACTS = Object.freeze({
  alloy: {
    flags: new Set(['--verbose']),
    values: { '--out-dir': 'artifact', '--repeat': { type: 'positiveInteger', max: 100 } },
  },
  tlc: {
    flags: new Set(),
    values: {
      '--out-dir': 'artifact',
      '--config': 'config',
      '--depth': { type: 'positiveInteger', max: 1000 },
      '--time-limit': { type: 'positiveInteger', max: 900 },
      '--workers': { type: 'positiveInteger', max: 32 },
      '--seed': { type: 'nonNegativeInteger', max: Number.MAX_SAFE_INTEGER },
    },
  },
  apalache: {
    flags: new Set(),
    values: {
      '--out-dir': 'artifact',
      '--config': 'config',
      '--length': { type: 'positiveInteger', max: 100 },
      '--init': 'identifier',
      '--next': 'identifier',
      '--inv': 'identifier',
    },
  },
  dafny: { flags: new Set(), values: {} },
  spin: { flags: new Set(), values: { '--out-dir': 'artifact', '--claim': 'identifier' } },
  nusmv: { flags: new Set(), values: {} },
  cbmc: { flags: new Set(), values: {} },
  quint: {
    flags: new Set(),
    values: {
      '--out-dir': 'artifact',
      '--seed': { type: 'nonNegativeInteger', max: Number.MAX_SAFE_INTEGER },
      '--max-samples': { type: 'positiveInteger', max: 10000 },
    },
  },
  prism: {
    flags: new Set(),
    values: { '--out-dir': 'artifact' },
  },
  tamarin: {
    flags: new Set(),
    values: {
      '--out-dir': 'artifact',
      '--time-limit': { type: 'positiveInteger', max: 900 },
    },
  },
  kani: {
    flags: new Set(),
    values: {
      '--out-dir': 'artifact',
      '--harness': 'identifier',
      '--unwind': { type: 'positiveInteger', max: 1000 },
    },
  },
});

function toPosixPath(value) {
  return value.split(path.sep).join('/');
}

function isSafeRepositoryPath(value, requiredPrefix) {
  if (typeof value !== 'string' || value.length === 0 || value.includes('\\')) return false;
  if (path.posix.isAbsolute(value) || value !== path.posix.normalize(value)) return false;
  if (value === '..' || value.startsWith('../') || value.includes('/../')) return false;
  return !requiredPrefix || value.startsWith(requiredPrefix);
}

function loadManifest(rootDir, manifestPath = MANIFEST_PATH) {
  const absolutePath = path.resolve(rootDir, manifestPath);
  let parsed;
  try {
    parsed = JSON.parse(fs.readFileSync(absolutePath, 'utf8'));
  } catch (error) {
    const wrapped = new Error(`manifest を読み込めません: ${manifestPath}: ${error.message}`);
    wrapped.cause = error;
    throw wrapped;
  }
  return { manifest: parsed, manifestPath: toPosixPath(manifestPath), absolutePath };
}

function expectedReferences(documentId) {
  if (/^chapter\d{2}$/.test(documentId)) {
    return [
      `src/ja/chapters/${documentId}.md`,
      `src/en/chapters/${documentId}.md`,
      `docs/chapters/${documentId}/index.md`,
      `docs/en/chapters/${documentId}/index.md`,
    ];
  }
  if (/^appendix-[a-z0-9]+(?:-[a-z0-9]+)*$/.test(documentId)) {
    return [
      `src/ja/appendices/${documentId}.md`,
      `src/en/appendices/${documentId}.md`,
      `docs/appendices/${documentId}/index.md`,
      `docs/en/appendices/${documentId}/index.md`,
    ];
  }
  return [];
}

function parseManifestCommand(entry) {
  if (!entry || typeof entry !== 'object' || typeof entry.command !== 'string') {
    throw new Error('command は string である必要があります');
  }
  const wrapper = TOOL_WRAPPERS[entry.tool];
  const optionContract = TOOL_OPTION_CONTRACTS[entry.tool];
  if (!wrapper || !optionContract) throw new Error(`未対応の tool です: ${String(entry.tool)}`);

  const tokens = entry.command.trim().split(/\s+/).filter(Boolean);
  if (tokens.length < 3 || tokens[0] !== 'bash' || tokens[1] !== wrapper) {
    throw new Error(`command は bash ${wrapper} と asset 引数で開始する必要があります`);
  }
  for (const token of tokens) {
    if (!/^[A-Za-z0-9_./:+=-]+$/.test(token) || token.includes('..') || token.includes('\\')) {
      throw new Error(`command token が許可されていません: ${token}`);
    }
  }

  const args = tokens.slice(2);
  const positional = [];
  const seenOptions = new Set();
  for (let index = 0; index < args.length; index += 1) {
    const token = args[index];
    if (!token.startsWith('-')) {
      positional.push(token);
      continue;
    }
    if (seenOptions.has(token)) throw new Error(`command option が重複しています: ${token}`);
    seenOptions.add(token);
    if (optionContract.flags.has(token)) continue;
    const valueContract = optionContract.values[token];
    if (!valueContract) throw new Error(`tool ${entry.tool} では許可されていない option です: ${token}`);
    const valueType = typeof valueContract === 'string' ? valueContract : valueContract.type;
    const value = args[index + 1];
    if (!value || value.startsWith('-')) throw new Error(`${token} の値がありません`);
    index += 1;

    if (valueType === 'artifact') {
      const expected = `.artifacts/manifest/${entry.id}/tool-output`;
      if (value !== expected) throw new Error(`${token} は ${expected} に固定してください`);
    } else if (valueType === 'config') {
      if (!entry.config || value !== entry.config) throw new Error(`${token} は manifest config と一致させてください`);
    } else if (valueType === 'positiveInteger') {
      if (!/^[1-9]\d*$/.test(value)) throw new Error(`${token} は正の整数にしてください`);
      if (typeof valueContract === 'object' && Number(value) > valueContract.max) {
        throw new Error(`${token} は ${valueContract.max} 以下にしてください`);
      }
    } else if (valueType === 'nonNegativeInteger') {
      if (!/^\d+$/.test(value)) throw new Error(`${token} は0以上の整数にしてください`);
      if (typeof valueContract === 'object' && Number(value) > valueContract.max) {
        throw new Error(`${token} は ${valueContract.max} 以下にしてください`);
      }
    } else if (valueType === 'identifier') {
      if (!/^[A-Za-z_][A-Za-z0-9_-]*$/.test(value)) throw new Error(`${token} の識別子が不正です`);
    }
  }

  const expectedAssets = Array.isArray(entry.assets) ? entry.assets : [];
  if (positional.length !== expectedAssets.length || positional.some((value, index) => value !== expectedAssets[index])) {
    throw new Error(`positional asset は manifest assets と同じ順序・件数にしてください: ${expectedAssets.join(' ')}`);
  }
  if (entry.config && optionContract.values['--config'] === 'config' && !seenOptions.has('--config')) {
    throw new Error('config entry には --config option が必要です');
  }

  return { executable: '/bin/bash', args: [wrapper, ...args] };
}

function validateManifest(manifest, options = {}) {
  const rootDir = path.resolve(options.rootDir || process.cwd());
  const checkFiles = options.checkFiles !== false;
  const manifestPath = options.manifestPath || MANIFEST_PATH;
  const errors = [];
  const ids = new Set();
  const assets = new Map();
  let toolManifest = options.toolManifest || null;

  function add(message, entryId = null) {
    errors.push({
      filePath: manifestPath,
      line: 1,
      message: entryId ? `[${entryId}] ${message}` : message,
    });
  }

  function validateExpected(expected, label, entryId) {
    if (!expected || typeof expected !== 'object' || Array.isArray(expected)) {
      add(`${label} は object である必要があります`, entryId);
      return;
    }
    if (!Number.isInteger(expected.exitCode) || expected.exitCode < 0) {
      add(`${label}.exitCode は0以上の integer である必要があります`, entryId);
    }
    if (typeof expected.stdoutMarker !== 'string' || expected.stdoutMarker.length === 0 || /[\r\n]/.test(expected.stdoutMarker)) {
      add(`${label}.stdoutMarker は改行を含まない空でない string である必要があります`, entryId);
    }
    if (!VALID_OUTCOMES.has(expected.outcome)) {
      add(`${label}.outcome は ${Array.from(VALID_OUTCOMES).join(' / ')} のいずれかである必要があります`, entryId);
    }
  }

  function validateLimits(limits, label, entryId) {
    if (!limits || typeof limits !== 'object' || Array.isArray(limits)) {
      add(`${label} は object である必要があります`, entryId);
      return;
    }
    for (const field of ['timeoutSeconds', 'memoryMiB']) {
      if (!Number.isSafeInteger(limits[field]) || limits[field] <= 0) {
        add(`${label}.${field} は正の safe integer である必要があります`, entryId);
      }
    }
    for (const field of ['seed', 'scope', 'depth', 'bound']) {
      if (!Object.prototype.hasOwnProperty.call(limits, field)) add(`${label}.${field} を明示してください`, entryId);
    }
    if (limits.seed !== null && typeof limits.seed !== 'string') add(`${label}.seed は string または null にしてください`, entryId);
    if (limits.scope !== null && typeof limits.scope !== 'string') add(`${label}.scope は string または null にしてください`, entryId);
    if (limits.depth !== null && (!Number.isSafeInteger(limits.depth) || limits.depth < 0)) {
      add(`${label}.depth は0以上の safe integer または null にしてください`, entryId);
    }
    if (limits.bound !== null && typeof limits.bound !== 'string') add(`${label}.bound は string または null にしてください`, entryId);
  }

  if (!manifest || typeof manifest !== 'object' || Array.isArray(manifest)) {
    add('manifest の最上位は object である必要があります');
    return errors;
  }
  if (manifest.schemaVersion !== 2) add('schemaVersion は 2 である必要があります');
  if (!Array.isArray(manifest.examples) || manifest.examples.length === 0) {
    add('examples は1件以上の配列である必要があります');
    return errors;
  }

  if (!toolManifest) {
    try {
      toolManifest = loadToolManifest(rootDir).manifest;
    } catch (error) {
      add(error.message);
    }
  }
  if (toolManifest) {
    for (const error of validateToolManifest(toolManifest, { rootDir, checkFiles })) {
      add(`tool manifest: ${error.message}`);
    }
  }

  for (const entry of manifest.examples) {
    const id = entry && typeof entry.id === 'string' ? entry.id : '(unknown)';
    if (!entry || typeof entry !== 'object' || Array.isArray(entry)) {
      add('各 example は object である必要があります');
      continue;
    }
    if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(entry.id || '')) {
      add('id は lowercase kebab-case である必要があります', id);
    } else if (ids.has(entry.id)) {
      add(`id が重複しています: ${entry.id}`, id);
    } else {
      ids.add(entry.id);
    }

    for (const field of ['tool', 'chapter', 'anchor', 'command', 'lane']) {
      if (typeof entry[field] !== 'string' || entry[field].trim() === '') {
        add(`${field} は空でない string である必要があります`, id);
      }
    }

    if (!DOCUMENT_PATTERN.test(entry.chapter || '')) {
      add('chapter は chapterNN または appendix-ID 形式である必要があります', id);
    }
    if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(entry.anchor || '')) {
      add('anchor は lowercase kebab-case である必要があります', id);
    }
    if (!VALID_LANES.has(entry.lane)) {
      add(`lane は ${Array.from(VALID_LANES).join(' / ')} のいずれかである必要があります`, id);
    }
    if (Object.prototype.hasOwnProperty.call(entry, 'version')) {
      add('version を example に重複記載せず tool manifest から参照してください', id);
    }
    if (toolManifest && typeof entry.tool === 'string') {
      const tool = getTool(toolManifest, entry.tool);
      if (!tool) add(`tool manifest に未登録です: ${entry.tool}`, id);
      else if (tool.lane !== entry.lane) add(`lane は tool manifest の ${tool.lane} と一致させてください`, id);
    }

    if (!Array.isArray(entry.references) || entry.references.length === 0) {
      add('references は1件以上の配列である必要があります', id);
    } else {
      const seenReferences = new Set();
      for (const reference of entry.references) {
        if (!isSafeRepositoryPath(reference) || !reference.endsWith('.md')) {
          add(`reference path が不正です: ${String(reference)}`, id);
          continue;
        }
        if (seenReferences.has(reference)) add(`reference が重複しています: ${reference}`, id);
        seenReferences.add(reference);
        if (checkFiles) {
          const absoluteReference = path.join(rootDir, reference);
          if (!fs.existsSync(absoluteReference) || !fs.statSync(absoluteReference).isFile()) {
            add(`reference file が存在しません: ${reference}`, id);
          }
        }
      }
    }

    if (!Array.isArray(entry.assets) || entry.assets.length === 0) {
      add('assets は1件以上の配列である必要があります', id);
    } else {
      for (const asset of entry.assets) {
        if (!isSafeRepositoryPath(asset, 'examples/')) {
          add(`asset path が不正です: ${String(asset)}`, id);
          continue;
        }
        const previousId = assets.get(asset);
        if (previousId && previousId !== entry.id) {
          add(`asset が複数 ID に登録されています: ${asset} (${previousId})`, id);
        } else {
          assets.set(asset, entry.id);
        }
        if (checkFiles) {
          const absoluteAsset = path.join(rootDir, asset);
          if (!fs.existsSync(absoluteAsset) || !fs.statSync(absoluteAsset).isFile()) {
            add(`asset file が存在しません: ${asset}`, id);
          }
        }
      }
    }

    if (entry.config !== null && !isSafeRepositoryPath(entry.config, 'examples/')) {
      add('config は null または examples/ 配下の path である必要があります', id);
    } else if (entry.config && checkFiles) {
      const absoluteConfig = path.join(rootDir, entry.config);
      if (!fs.existsSync(absoluteConfig) || !fs.statSync(absoluteConfig).isFile()) {
        add(`config file が存在しません: ${entry.config}`, id);
      }
    }

    const wrapper = TOOL_WRAPPERS[entry.tool];
    if (wrapper && checkFiles && !fs.existsSync(path.join(rootDir, wrapper))) {
      add(`tool wrapper が存在しません: ${wrapper}`, id);
    }
    if (typeof entry.command === 'string') {
      try {
        parseManifestCommand(entry);
      } catch (error) {
        add(error.message, id);
      }
    }

    validateExpected(entry.expected, 'expected', id);
    validateLimits(entry.limits, 'limits', id);

    if (entry.profiles !== undefined) {
      if (!entry.profiles || typeof entry.profiles !== 'object' || Array.isArray(entry.profiles)) {
        add('profiles は object である必要があります', id);
      } else {
        for (const [profileName, profile] of Object.entries(entry.profiles)) {
          if (profileName !== 'nightly') add(`未対応の profile です: ${profileName}`, id);
          if (!profile || typeof profile !== 'object' || Array.isArray(profile)) {
            add(`profiles.${profileName} は object である必要があります`, id);
            continue;
          }
          if (typeof profile.command !== 'string' || profile.command.trim() === '') {
            add(`profiles.${profileName}.command は空でない string である必要があります`, id);
          } else {
            try {
              parseManifestCommand({ ...entry, ...profile, id: `${entry.id}--${profileName}` });
            } catch (error) {
              add(`profiles.${profileName}: ${error.message}`, id);
            }
          }
          validateLimits(profile.limits, `profiles.${profileName}.limits`, id);
          if (profile.expected !== undefined) validateExpected(profile.expected, `profiles.${profileName}.expected`, id);
        }
      }
    }
  }

  return errors;
}

function runnerCommand(id) {
  return `node scripts/run-example-manifest.js --id ${id}`;
}

module.exports = {
  DOCUMENT_PATTERN,
  MANIFEST_PATH,
  TOOL_WRAPPERS,
  VALID_LANES,
  VALID_OUTCOMES,
  expectedReferences,
  isSafeRepositoryPath,
  loadManifest,
  parseManifestCommand,
  runnerCommand,
  validateManifest,
};
