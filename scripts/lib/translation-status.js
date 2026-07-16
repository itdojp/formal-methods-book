'use strict';

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');
const { resolveWithinRoot } = require('./publication-metadata');

const ALLOWED_STATUSES = new Set(['synced', 'partial', 'stale']);
const TOOL_LABEL_GROUPS = {
  tool_compliant: [
    '【ツール準拠（そのまま動く）】',
    '〖ツール準拠（そのまま動く）〗',
    '【Tool-compliant (runs as-is)】',
    '〖Tool-compliant (runs as-is)〗',
  ],
  context_dependent: [
    '【文脈依存スニペット】',
    '〖文脈依存スニペット〗',
    '【Context-dependent snippet】',
    '〖Context-dependent snippet〗',
  ],
  pseudo_notation: [
    '【擬似記法】',
    '〖擬似記法〗',
    '【Pseudo notation】',
    '〖Pseudo notation〗',
  ],
};
const STRICT_TOOL_LABELS = Object.values(TOOL_LABEL_GROUPS).flat();
const LEGACY_STATUS_PATTERN = /^> Translation status:|^> Japanese source of truth:/m;

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function sha256(content) {
  return crypto.createHash('sha256').update(content).digest('hex');
}

function expectedPagePaths(config) {
  return [
    'index.md',
    ...(config.structure?.chapters || []).map((entry) => `chapters/${entry.id}.md`),
    ...(config.structure?.appendices || []).map((entry) => `appendices/${entry.id}.md`),
    ...(config.structure?.specialPages || []).map((entry) => `${entry.id}/index.md`),
  ].sort();
}

function loadTranslationManifest(repoRoot, publicationModel) {
  const relativePath = publicationModel.manifest.translation?.statusManifest;
  if (relativePath !== 'translation-status.json') {
    throw new Error('book-config.json translation.statusManifest must be translation-status.json');
  }
  return readJson(resolveWithinRoot(repoRoot, relativePath, 'translation status manifest'));
}

function isValidDate(value) {
  if (typeof value !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(value)) return false;
  const date = new Date(`${value}T00:00:00Z`);
  return !Number.isNaN(date.getTime()) && date.toISOString().slice(0, 10) === value;
}

function validateTranslationManifest(manifest, publicationModel) {
  const errors = [];
  const sourceLocale = manifest?.source_locale;
  const translationLocale = manifest?.translation_locale;
  const sourceEdition = publicationModel.manifest.editions?.[sourceLocale];
  const translationEdition = publicationModel.manifest.editions?.[translationLocale];

  if (manifest?.schema_version !== '1.0') errors.push('translation-status.json schema_version must be 1.0');
  if (sourceLocale !== publicationModel.manifest.project?.defaultEdition) {
    errors.push('translation-status.json source_locale must match the default edition');
  }
  if (!sourceEdition || !translationEdition || translationEdition.translationOf !== sourceLocale) {
    errors.push('translation-status.json locales must identify the configured source and translation editions');
  }
  if (!Number.isInteger(manifest?.policy?.max_sync_age_days) || manifest.policy.max_sync_age_days < 1) {
    errors.push('translation-status.json policy.max_sync_age_days must be a positive integer');
  }
  if (manifest?.policy?.partial_stale_release !== 'visible-status-and-artifact-required') {
    errors.push('translation-status.json policy.partial_stale_release has an unsupported value');
  }
  if (manifest?.policy?.report_path !== '.artifacts/translation-status/report.json') {
    errors.push('translation-status.json policy.report_path must be .artifacts/translation-status/report.json');
  }
  if (!manifest?.pages || typeof manifest.pages !== 'object' || Array.isArray(manifest.pages)) {
    errors.push('translation-status.json pages must be an object');
    return errors;
  }
  if (!sourceEdition || !translationEdition) return errors;

  const expected = expectedPagePaths(publicationModel.editions[sourceLocale]);
  const actual = Object.keys(manifest.pages).sort();
  const missing = expected.filter((relativePath) => !actual.includes(relativePath));
  const unexpected = actual.filter((relativePath) => !expected.includes(relativePath));
  if (missing.length > 0) errors.push(`translation-status.json missing pages: ${missing.join(', ')}`);
  if (unexpected.length > 0) errors.push(`translation-status.json unexpected pages: ${unexpected.join(', ')}`);

  for (const relativePath of actual) {
    const entry = manifest.pages[relativePath];
    const label = `translation-status.json pages.${relativePath}`;
    if (!entry || typeof entry !== 'object' || Array.isArray(entry)) {
      errors.push(`${label} must be an object`);
      continue;
    }
    const expectedSource = `${sourceEdition.sourceRoot}/${relativePath}`;
    const expectedTranslation = `${translationEdition.sourceRoot}/${relativePath}`;
    if (entry.source_path !== expectedSource) errors.push(`${label}.source_path must be ${expectedSource}`);
    if (entry.translation_path !== expectedTranslation) {
      errors.push(`${label}.translation_path must be ${expectedTranslation}`);
    }
    for (const key of ['source_commit', 'translated_commit']) {
      if (typeof entry[key] !== 'string' || !/^[0-9a-f]{40}$/.test(entry[key])) {
        errors.push(`${label}.${key} must be a full lowercase Git commit SHA`);
      }
    }
    for (const key of ['source_sha256', 'translation_sha256']) {
      if (typeof entry[key] !== 'string' || !/^[0-9a-f]{64}$/.test(entry[key])) {
        errors.push(`${label}.${key} must be a lowercase SHA-256 digest`);
      }
    }
    if (!ALLOWED_STATUSES.has(entry.status)) errors.push(`${label}.status must be synced, partial, or stale`);
    if (!isValidDate(entry.reviewed_at)) errors.push(`${label}.reviewed_at must be a valid YYYY-MM-DD date`);
    if (entry.reviewed_by !== undefined && (typeof entry.reviewed_by !== 'string' || !entry.reviewed_by.trim())) {
      errors.push(`${label}.reviewed_by must be a non-empty string when present`);
    }
    if (entry.status !== 'synced') {
      if (typeof entry.tracking_issue !== 'string'
          || !/^https:\/\/github\.com\/itdojp\/formal-methods-book\/issues\/\d+$/.test(entry.tracking_issue)) {
        errors.push(`${label}.tracking_issue is required for partial/stale pages`);
      }
      if (typeof entry.notes !== 'string' || !entry.notes.trim()) {
        errors.push(`${label}.notes is required for partial/stale pages`);
      }
    }
  }
  return errors;
}

function extractMarkdownDestinations(content) {
  const visibleContent = content
    .split(/\r?\n/)
    .reduce((state, line) => {
      const fenceMatch = line.match(/^ {0,3}(`{3,}|~{3,})(.*)$/);
      if (fenceMatch) {
        const marker = fenceMatch[1];
        if (!state.fence) {
          state.fence = { character: marker[0], length: marker.length };
        } else if (marker[0] === state.fence.character && marker.length >= state.fence.length) {
          state.fence = null;
        }
        state.lines.push('');
        return state;
      }
      if (state.fence) {
        state.lines.push('');
        return state;
      }

      let visibleLine = line;
      for (let offset = 0; offset < visibleLine.length;) {
        if (visibleLine[offset] !== '`') {
          offset += 1;
          continue;
        }
        let runEnd = offset;
        while (visibleLine[runEnd] === '`') runEnd += 1;
        const marker = visibleLine.slice(offset, runEnd);
        const closing = visibleLine.indexOf(marker, runEnd);
        if (closing < 0) break;
        visibleLine = `${visibleLine.slice(0, offset)}${' '.repeat(closing + marker.length - offset)}`
          + visibleLine.slice(closing + marker.length);
        offset = closing + marker.length;
      }
      state.lines.push(visibleLine);
      return state;
    }, { fence: null, lines: [] })
    .lines
    .join('\n')
    .replace(/<!--[\s\S]*?-->/g, '');

  const destinations = [];
  let offset = 0;
  while (offset < visibleContent.length) {
    const start = visibleContent.indexOf('](', offset);
    if (start < 0) break;
    let depth = 1;
    let escaped = false;
    let index = start + 2;
    for (; index < visibleContent.length; index += 1) {
      const character = visibleContent[index];
      if (escaped) {
        escaped = false;
        continue;
      }
      if (character === '\\') {
        escaped = true;
        continue;
      }
      if (character === '(') depth += 1;
      if (character === ')') {
        depth -= 1;
        if (depth === 0) break;
      }
    }
    if (depth === 0) {
      let destination = visibleContent.slice(start + 2, index).trim();
      if (destination.startsWith('<')) {
        const closingBracket = destination.indexOf('>');
        destination = closingBracket >= 0
          ? destination.slice(1, closingBracket)
          : destination;
      } else {
        destination = destination.split(/\s+(?=["'(])/u, 1)[0];
      }
      destinations.push(destination);
      offset = index + 1;
    } else {
      break;
    }
  }
  for (const match of visibleContent.matchAll(/^ {0,3}\[[^\]\r\n]+\]:[ \t]*(?:<([^>\r\n]+)>|(\S+))/gm)) {
    destinations.push(match[1] || match[2]);
  }
  for (const match of visibleContent.matchAll(/<((?:https):\/\/[^>]+)>/g)) destinations.push(match[1]);
  return [...new Set(destinations)];
}

function tableColumnCount(line) {
  const trimmed = line.trim();
  const body = trimmed.startsWith('|') ? trimmed.slice(1) : trimmed;
  const withoutEnd = body.endsWith('|') ? body.slice(0, -1) : body;
  return withoutEnd.split(/(?<!\\)\|/).length;
}

function analyzeMarkdown(content) {
  const headings = [];
  const codeFences = [];
  const tableColumns = [];
  const lines = content.split(/\r?\n/);
  let fence = null;

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const fenceMatch = line.match(/^ {0,3}(`{3,}|~{3,})(.*)$/);
    if (fenceMatch) {
      const marker = fenceMatch[1];
      if (!fence) {
        fence = { character: marker[0], length: marker.length };
        const info = fenceMatch[2].trim();
        codeFences.push(info ? info.split(/\s+/)[0].replace(/^\{\.?|\}$/g, '') : '');
      } else if (marker[0] === fence.character && marker.length >= fence.length) {
        fence = null;
      }
      continue;
    }
    if (fence) continue;

    const headingMatch = line.match(/^ {0,3}(#{1,6})\s+(.+?)\s*#*\s*$/);
    if (headingMatch) {
      const text = headingMatch[2].trim();
      const numbered = text.match(/^((?:\d+|[A-Z])(?:\.\d+)+)\b/);
      headings.push({
        level: headingMatch[1].length,
        numbered_id: numbered ? numbered[1] : null,
      });
    }

    if (index + 1 < lines.length && line.includes('|')) {
      const separator = lines[index + 1];
      if (/^\s*\|?\s*:?-{3,}:?\s*(?:\|\s*:?-{3,}:?\s*)+\|?\s*$/.test(separator)) {
        tableColumns.push(tableColumnCount(line));
      }
    }
  }

  const destinations = extractMarkdownDestinations(content);
  const externalLinks = [...new Set(destinations.filter((destination) => destination.startsWith('https://'))) ].sort();
  const examplePaths = [...new Set(content.match(/examples\/[A-Za-z0-9_./-]+/g) || [])].sort();
  const toolLabels = Object.fromEntries(Object.entries(TOOL_LABEL_GROUPS).map(([kind, labels]) => [
    kind,
    labels.reduce((count, label) => count + content.split(label).length - 1, 0),
  ]));
  return {
    heading_levels: headings.map((heading) => heading.level),
    numbered_heading_ids: headings.filter((heading) => heading.numbered_id).map((heading) => heading.numbered_id),
    code_fence_languages: codeFences,
    table_columns: tableColumns,
    tool_labels: toolLabels,
    example_paths: examplePaths,
    external_reference_links: externalLinks,
  };
}

function arraysEqual(left, right) {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function objectsEqual(left, right) {
  return JSON.stringify(left) === JSON.stringify(right);
}

function compareTranslationFeatures(source, translation) {
  const mismatches = [];
  if (!arraysEqual(source.heading_levels, translation.heading_levels)) mismatches.push('heading_structure');
  if (!arraysEqual(source.numbered_heading_ids, translation.numbered_heading_ids)) {
    mismatches.push('numbered_heading_ids');
  }
  if (!arraysEqual(source.code_fence_languages, translation.code_fence_languages)) mismatches.push('code_blocks');
  if (!arraysEqual(source.table_columns, translation.table_columns)) mismatches.push('tables');
  if (!objectsEqual(source.tool_labels, translation.tool_labels)) mismatches.push('tool_labels');
  if (!arraysEqual(source.example_paths, translation.example_paths)) mismatches.push('example_paths');
  if (!arraysEqual(source.external_reference_links, translation.external_reference_links)) {
    mismatches.push('external_reference_links');
  }
  return mismatches;
}

function defaultReadCommitFile(repoRoot, commit, filePath) {
  return execFileSync('git', ['show', `${commit}:${filePath}`], {
    cwd: repoRoot,
    encoding: null,
    maxBuffer: 32 * 1024 * 1024,
    stdio: ['ignore', 'pipe', 'pipe'],
  });
}

function defaultIsCommitAncestor(repoRoot, commit) {
  try {
    execFileSync('git', ['merge-base', '--is-ancestor', commit, 'HEAD'], {
      cwd: repoRoot,
      stdio: ['ignore', 'ignore', 'pipe'],
    });
    return true;
  } catch {
    return false;
  }
}

function daysBetween(dateString, now) {
  const reviewed = new Date(`${dateString}T00:00:00Z`);
  return Math.floor((now.getTime() - reviewed.getTime()) / 86400000);
}

function evaluateTranslationStatus({
  repoRoot,
  publicationModel,
  manifest,
  now = new Date(),
  readCommitFile = defaultReadCommitFile,
  isCommitAncestor = defaultIsCommitAncestor,
}) {
  const errors = validateTranslationManifest(manifest, publicationModel);
  const warnings = [];
  const pages = [];
  if (errors.length > 0) return { errors, warnings, pages, summary: {} };
  const ancestorCache = new Map();

  for (const [relativePath, entry] of Object.entries(manifest.pages).sort(([left], [right]) => left.localeCompare(right))) {
    const pageErrors = [];
    const pageWarnings = [];
    const sourceFile = resolveWithinRoot(repoRoot, entry.source_path, `${relativePath} source path`);
    const translationFile = resolveWithinRoot(repoRoot, entry.translation_path, `${relativePath} translation path`);
    const sourceContent = fs.readFileSync(sourceFile);
    const translationContent = fs.readFileSync(translationFile);
    const currentSourceDigest = sha256(sourceContent);
    const currentTranslationDigest = sha256(translationContent);
    const sourceChanged = currentSourceDigest !== entry.source_sha256;
    const translationChanged = currentTranslationDigest !== entry.translation_sha256;

    for (const [label, commit] of [
      ['source_commit', entry.source_commit],
      ['translated_commit', entry.translated_commit],
    ]) {
      if (!ancestorCache.has(commit)) ancestorCache.set(commit, isCommitAncestor(repoRoot, commit));
      if (!ancestorCache.get(commit)) pageErrors.push(`${label} is not an ancestor of HEAD`);
    }

    try {
      if (sha256(readCommitFile(repoRoot, entry.source_commit, entry.source_path)) !== entry.source_sha256) {
        pageErrors.push('source_commit does not contain source_sha256');
      }
    } catch (error) {
      pageErrors.push(`source_commit snapshot cannot be read: ${error.message}`);
    }
    try {
      if (sha256(readCommitFile(repoRoot, entry.translated_commit, entry.translation_path))
          !== entry.translation_sha256) {
        pageErrors.push('translated_commit does not contain translation_sha256');
      }
    } catch (error) {
      pageErrors.push(`translated_commit snapshot cannot be read: ${error.message}`);
    }

    const translationText = translationContent.toString('utf8');
    if (LEGACY_STATUS_PATTERN.test(translationText)) {
      pageErrors.push('legacy free-text translation status header is forbidden');
    }
    const sourceFeatures = analyzeMarkdown(sourceContent.toString('utf8'));
    const translationFeatures = analyzeMarkdown(translationText);
    const mismatches = compareTranslationFeatures(sourceFeatures, translationFeatures);

    if (entry.status === 'synced') {
      if (sourceChanged || translationChanged) pageErrors.push('synced snapshot has content drift');
      if (mismatches.length > 0) pageErrors.push(`synced structure differs: ${mismatches.join(', ')}`);
    } else if (entry.status === 'partial') {
      if (sourceChanged || translationChanged) pageErrors.push('partial snapshot has content drift; mark stale or re-review');
      pageWarnings.push(`partial translation: ${mismatches.join(', ') || 'semantic review remains incomplete'}`);
    } else {
      if (!sourceChanged && !translationChanged) pageWarnings.push('stale status has no current digest drift');
      pageWarnings.push(`stale translation: ${mismatches.join(', ') || 're-review required'}`);
    }

    const reviewAgeDays = daysBetween(entry.reviewed_at, now);
    if (reviewAgeDays < 0) {
      pageErrors.push('reviewed_at cannot be in the future');
    } else if (entry.status === 'synced' && reviewAgeDays > manifest.policy.max_sync_age_days) {
      pageErrors.push(
        `synced review exceeds max_sync_age_days (${reviewAgeDays} > ${manifest.policy.max_sync_age_days}); `
          + 're-review or mark stale',
      );
    } else if (reviewAgeDays > manifest.policy.max_sync_age_days) {
      pageWarnings.push(`translation review is ${reviewAgeDays} days old`);
    }

    for (const message of pageErrors) errors.push(`${relativePath}: ${message}`);
    for (const message of pageWarnings) warnings.push(`${relativePath}: ${message}`);
    pages.push({
      relative_path: relativePath,
      status: entry.status,
      source_path: entry.source_path,
      translation_path: entry.translation_path,
      source_commit: entry.source_commit,
      translated_commit: entry.translated_commit,
      reviewed_at: entry.reviewed_at,
      reviewed_by: entry.reviewed_by || null,
      tracking_issue: entry.tracking_issue || null,
      notes: entry.notes || null,
      source_changed: sourceChanged,
      translation_changed: translationChanged,
      mismatches,
      source_features: sourceFeatures,
      translation_features: translationFeatures,
      errors: pageErrors,
      warnings: pageWarnings,
    });
  }

  const statusCounts = Object.fromEntries([...ALLOWED_STATUSES].map((status) => [
    status,
    pages.filter((page) => page.status === status).length,
  ]));
  return {
    errors,
    warnings,
    pages,
    summary: {
      total_pages: pages.length,
      status_counts: statusCounts,
      pages_with_mismatches: pages.filter((page) => page.mismatches.length > 0).length,
      errors: errors.length,
      warnings: warnings.length,
    },
  };
}

function statusLabel(status) {
  return { synced: 'Synced', partial: 'Partial', stale: 'Stale' }[status];
}

function renderTranslationNotice(entry) {
  const shortCommit = entry.source_commit.slice(0, 12);
  const commitUrl = `https://github.com/itdojp/formal-methods-book/commit/${entry.source_commit}`;
  const lines = [
    `> **Translation status: ${statusLabel(entry.status)}.** `
      + `Reviewed against Japanese source commit [\`${shortCommit}\`](${commitUrl}) on ${entry.reviewed_at}.`,
  ];
  if (entry.status === 'partial') {
    lines.push(`> Some content, headings, examples, tables, or references remain partially synchronized. `
      + `[Track the remaining work](${entry.tracking_issue}).`);
  } else if (entry.status === 'stale') {
    lines.push(`> The Japanese source or this translation changed after the recorded review. `
      + `[Track the resynchronization](${entry.tracking_issue}).`);
  }
  return `${lines.join('\n')}\n`;
}

function insertTranslationNotice(content, entry) {
  const heading = content.match(/^# [^\r\n]+\r?\n/);
  if (!heading) throw new Error(`${entry.translation_path}: level-1 heading must be the first line`);
  return `${heading[0]}\n${renderTranslationNotice(entry)}\n${content.slice(heading[0].length).replace(/^\r?\n/, '')}`;
}

module.exports = {
  ALLOWED_STATUSES,
  LEGACY_STATUS_PATTERN,
  STRICT_TOOL_LABELS,
  analyzeMarkdown,
  compareTranslationFeatures,
  evaluateTranslationStatus,
  expectedPagePaths,
  extractMarkdownDestinations,
  insertTranslationNotice,
  loadTranslationManifest,
  renderTranslationNotice,
  sha256,
  validateTranslationManifest,
};
