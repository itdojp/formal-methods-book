'use strict';

const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const SEARCH_INDEX_SCHEMA_VERSION = 1;
const SEARCH_INDEX_MAX_BYTES = 4 * 1024 * 1024;

function toPosix(filePath) {
  return filePath.split(path.sep).join('/');
}

function assertSafeOutput(repoRoot, targetPath, label) {
  const root = path.resolve(repoRoot);
  const target = path.resolve(targetPath);
  if (target !== root && !target.startsWith(`${root}${path.sep}`)) {
    throw new Error(`${label}: path escapes repository root`);
  }
  let current = root;
  for (const segment of path.relative(root, target).split(path.sep).filter(Boolean)) {
    current = path.join(current, segment);
    const entry = fs.lstatSync(current, { throwIfNoEntry: false });
    if (entry?.isSymbolicLink()) {
      throw new Error(`${label}: symbolic link path component is not allowed: ${toPosix(path.relative(root, current))}`);
    }
  }
}

function normalizeSearchText(value) {
  return String(value || '')
    .normalize('NFKC')
    .toLocaleLowerCase('en-US')
    .replace(/\s+/g, ' ')
    .trim();
}

function stripInlineMarkdown(value) {
  return String(value || '')
    .replace(/\{:\s*#[A-Za-z0-9_.:-]+\s*\}\s*$/u, '')
    .replace(/\{#[A-Za-z0-9_.:-]+\}\s*$/u, '')
    .replace(/!\[([^\]]*)\]\([^)]*\)/gu, '$1')
    .replace(/\[([^\]]+)\]\([^)]*\)/gu, '$1')
    .replace(/\[([^\]]+)\]\[[^\]]*\]/gu, '$1')
    .replace(/<https?:\/\/[^>]+>/gu, '')
    .replace(/<[^>]+>/gu, '')
    .replace(/\{[{%][\s\S]*?[%}]\}/gu, '')
    .replace(/[`*_~]/gu, '')
    .replace(/&nbsp;/gu, ' ')
    .replace(/&amp;/gu, '&')
    .replace(/&lt;/gu, '<')
    .replace(/&gt;/gu, '>')
    .replace(/\s+/gu, ' ')
    .trim();
}

function baseKramdownId(heading) {
  const raw = String(heading || '');
  const explicit = raw.match(/\{#([A-Za-z0-9_.:-]+)\}\s*$/u);
  if (explicit) return explicit[1];

  // Kramdown treats a same-line `{: #id }` as visible heading text rather
  // than an inline attribute list. Preserve its observed auto-id shape.
  const sameLineBlockAttribute = raw.match(/^(.*)\{:\s*#([A-Za-z0-9_.:-]+)\s*\}\s*$/u);
  if (sameLineBlockAttribute) {
    return `${baseKramdownId(sameLineBlockAttribute[1])}-${sameLineBlockAttribute[2]}-`;
  }

  const cleaned = stripInlineMarkdown(raw)
    .toLocaleLowerCase('en-US')
    .replace(/[^\p{L}\p{M}\p{N}\p{Pc}\- ]/gu, '')
    .replace(/ /gu, '-');
  return cleaned || 'section';
}

function uniqueKramdownId(heading, usedIds, explicitId = null) {
  const base = explicitId || baseKramdownId(heading);
  if (!usedIds.has(base)) {
    usedIds.add(base);
    return base;
  }
  let suffix = 1;
  while (usedIds.has(`${base}-${suffix}`)) suffix += 1;
  const value = `${base}-${suffix}`;
  usedIds.add(value);
  return value;
}

function glossaryTermId(term, usedIds) {
  const base = `glossary-${baseKramdownId(term)}`;
  if (!usedIds.has(base)) {
    usedIds.add(base);
    return base;
  }
  let suffix = 1;
  while (usedIds.has(`${base}-${suffix}`)) suffix += 1;
  const value = `${base}-${suffix}`;
  usedIds.add(value);
  return value;
}

function addGlossaryTermAnchors(markdown) {
  const usedIds = new Set();
  return String(markdown).split(/\r?\n/u).map((line) => {
    const existing = line.match(/^<span\s+id="([^"]+)"[^>]*><\/span>/u);
    if (existing) {
      usedIds.add(existing[1]);
      return line;
    }
    const term = line.match(/^(\*\*([^*\r\n]+)\*\*)(\s*[:：].*)$/u);
    if (!term) return line;
    const id = glossaryTermId(stripInlineMarkdown(term[2]), usedIds);
    return `<span id="${id}" class="search-term-anchor" aria-hidden="true"></span>${line}`;
  }).join('\n');
}

function removeFrontMatter(markdown) {
  return String(markdown).replace(/^---\r?\n[\s\S]*?\r?\n---\r?\n/u, '');
}

function removeHtmlComments(markdown) {
  return String(markdown).replace(/<!--[\s\S]*?-->/gu, '');
}

function appendText(entry, value) {
  const text = stripInlineMarkdown(value)
    .replace(/^[-+*]\s+/u, '')
    .replace(/^\d+[.)]\s+/u, '')
    .replace(/^>\s?/u, '')
    .replace(/^\|/u, '')
    .replace(/\|$/u, '')
    .replace(/\s*\|\s*/gu, ' · ')
    .trim();
  if (!text || /^[-:| ]+$/u.test(text)) return;
  if (entry.textLines.at(-1) !== text) entry.textLines.push(text);
}

function extractExplicitId(rawHeading, nextLine) {
  const inline = rawHeading.match(/\{#([A-Za-z0-9_.:-]+)\}\s*$/u);
  if (inline) return { id: inline[1], consumeNext: false };
  const following = String(nextLine || '').match(/^\s*\{:\s*#([A-Za-z0-9_.:-]+)\s*\}\s*$/u);
  return following ? { id: following[1], consumeNext: true } : { id: null, consumeNext: false };
}

function parseMarkdownSections(markdown, descriptor) {
  const lines = removeHtmlComments(removeFrontMatter(markdown)).split(/\r?\n/u);
  const entries = [];
  const usedIds = new Set();
  let current = null;
  let fence = null;

  function startEntry({ heading, anchor, kind = 'heading' }) {
    current = { heading, anchor, kind, textLines: [] };
    entries.push(current);
  }

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    const fenceMatch = line.match(/^\s*(`{3,}|~{3,})/u);
    if (fenceMatch) {
      const marker = fenceMatch[1][0];
      if (!fence) fence = marker;
      else if (fence === marker) fence = null;
      continue;
    }
    if (fence) continue;

    const headingMatch = line.match(/^(#{1,6})\s+(.+?)\s*$/u);
    if (headingMatch) {
      const explicit = extractExplicitId(headingMatch[2], lines[index + 1]);
      const heading = stripInlineMarkdown(headingMatch[2]);
      const anchor = uniqueKramdownId(headingMatch[2], usedIds, explicit.id);
      startEntry({ heading, anchor });
      if (explicit.consumeNext) index += 1;
      continue;
    }

    const termMatch = line.match(/^<span\s+id="([^"]+)"[^>]*><\/span>\s*\*\*([^*\r\n]+)\*\*\s*[:：]\s*(.*)$/u);
    if (termMatch) {
      usedIds.add(termMatch[1]);
      startEntry({ heading: stripInlineMarkdown(termMatch[2]), anchor: termMatch[1], kind: 'term' });
      appendText(current, termMatch[3]);
      continue;
    }

    if (/^\s*\{:\s*#[A-Za-z0-9_.:-]+\s*\}\s*$/u.test(line)) continue;
    if (/^\s*\{[{%]/u.test(line) || /^\s*[}%}]\}\s*$/u.test(line)) continue;
    if (!current) {
      startEntry({ heading: descriptor.title, anchor: null, kind: 'page' });
    }
    appendText(current, line);
  }

  if (entries.length === 0) {
    startEntry({ heading: descriptor.title, anchor: null, kind: 'page' });
  }
  return entries;
}

function loadAliasManifest(repoRoot) {
  const manifest = JSON.parse(fs.readFileSync(path.join(repoRoot, 'search-aliases.json'), 'utf8'));
  const errors = [];
  if (manifest.schemaVersion !== 1) errors.push('search-aliases.json schemaVersion must be 1');
  if (!Array.isArray(manifest.groups) || manifest.groups.length === 0) {
    errors.push('search-aliases.json groups must be a non-empty array');
  }
  const ids = new Set();
  const normalizedTerms = new Map();
  for (const [index, group] of (manifest.groups || []).entries()) {
    if (typeof group?.id !== 'string' || !group.id.trim()) errors.push(`groups[${index}].id is required`);
    if (ids.has(group?.id)) errors.push(`duplicate alias group id: ${group.id}`);
    ids.add(group?.id);
    if (!Array.isArray(group?.terms) || group.terms.length < 2) {
      errors.push(`groups[${index}].terms must contain at least two terms`);
      continue;
    }
    const groupTerms = new Set();
    for (const term of group.terms) {
      if (typeof term !== 'string') {
        errors.push(`groups[${index}] terms must be strings`);
        continue;
      }
      const normalized = normalizeSearchText(term);
      if (!normalized) errors.push(`groups[${index}] contains an empty term`);
      if (groupTerms.has(normalized)) errors.push(`groups[${index}] contains duplicate term ${JSON.stringify(term)}`);
      groupTerms.add(normalized);
      const owner = normalizedTerms.get(normalized);
      if (owner && owner !== group.id) errors.push(`alias term ${JSON.stringify(term)} is shared by ${owner} and ${group.id}`);
      normalizedTerms.set(normalized, group.id);
    }
  }
  if (errors.length > 0) throw new Error(`Invalid search alias manifest:\n- ${errors.join('\n- ')}`);
  return manifest;
}

function pageDescriptors(model, locale) {
  const edition = model.manifest.editions[locale];
  const config = model.editions[locale];
  const descriptors = [{
    id: 'home',
    section: 'root',
    title: config.title,
    description: config.description,
    path: edition.canonicalBasePath,
    order: -1,
    outputPath: toPosix(path.join(edition.publishRoot, 'index.md')),
  }];
  for (const entry of config.structure.specialPages || []) {
    descriptors.push({
      ...entry,
      section: 'special',
      outputPath: toPosix(path.join(edition.publishRoot, entry.id, 'index.md')),
    });
  }
  for (const entry of config.structure.chapters || []) {
    descriptors.push({
      ...entry,
      section: 'chapters',
      outputPath: toPosix(path.join(edition.publishRoot, 'chapters', entry.id, 'index.md')),
    });
  }
  for (const entry of config.structure.appendices || []) {
    descriptors.push({
      ...entry,
      section: 'appendices',
      outputPath: toPosix(path.join(edition.publishRoot, 'appendices', entry.id, 'index.md')),
    });
  }
  return descriptors.sort((left, right) => left.order - right.order || left.id.localeCompare(right.id));
}

function aliasesForEntry(entry, aliasManifest) {
  const haystack = normalizeSearchText(`${entry.title} ${entry.chapter} ${entry.heading} ${entry.text}`);
  const aliases = [];
  for (const group of aliasManifest.groups) {
    if (!group.terms.some((term) => haystack.includes(normalizeSearchText(term)))) continue;
    for (const term of group.terms) {
      if (!haystack.includes(normalizeSearchText(term)) && !aliases.includes(term)) aliases.push(term);
    }
  }
  return aliases;
}

function renderSearchIndex({ repoRoot, model, locale, pages }) {
  const aliasManifest = loadAliasManifest(repoRoot);
  const baseUrl = `/${model.manifest.project.id}`;
  const entries = [];
  for (const descriptor of pageDescriptors(model, locale)) {
    const markdown = pages.get(descriptor.outputPath);
    if (typeof markdown !== 'string') {
      throw new Error(`${locale}: search source is missing generated page ${descriptor.outputPath}`);
    }
    for (const [sectionIndex, section] of parseMarkdownSections(markdown, descriptor).entries()) {
      const pageUrl = `${baseUrl}${descriptor.path}`.replace(/\/{2,}/gu, '/');
      const url = section.anchor ? `${pageUrl}#${section.anchor}` : pageUrl;
      const text = section.textLines.join(' ').replace(/\s+/gu, ' ').trim() || section.heading;
      const entry = {
        id: crypto.createHash('sha256').update(`${locale}\0${url}\0${section.heading}\0${sectionIndex}`).digest('hex').slice(0, 16),
        locale,
        pageId: descriptor.id,
        section: descriptor.section,
        title: section.heading,
        chapter: descriptor.title,
        heading: section.heading,
        url,
        text,
        aliases: [],
      };
      entry.aliases = aliasesForEntry(entry, aliasManifest);
      entries.push(entry);
    }
  }
  return {
    schemaVersion: SEARCH_INDEX_SCHEMA_VERSION,
    project: model.manifest.project.id,
    projectVersion: model.manifest.project.version,
    locale,
    entryCount: entries.length,
    entries,
  };
}

function searchIndexOutputPath(model, locale) {
  const defaultEdition = model.manifest.editions[model.manifest.project.defaultEdition];
  return toPosix(path.join(defaultEdition.publishRoot, 'assets', `search-index.${locale}.json`));
}

function serializeSearchIndex(index) {
  return `${JSON.stringify(index, null, 2)}\n`;
}

function writeSearchIndex(repoRoot, model, locale, pages) {
  const started = process.hrtime.bigint();
  const index = renderSearchIndex({ repoRoot, model, locale, pages });
  const output = serializeSearchIndex(index);
  const outputPath = searchIndexOutputPath(model, locale);
  const outputFile = path.join(repoRoot, outputPath);
  assertSafeOutput(repoRoot, outputFile, `${locale} search index output`);
  fs.mkdirSync(path.dirname(outputFile), { recursive: true });
  fs.writeFileSync(outputFile, output);
  const elapsedMs = Number(process.hrtime.bigint() - started) / 1e6;
  return { outputPath, bytes: Buffer.byteLength(output), entries: index.entryCount, elapsedMs };
}

module.exports = {
  SEARCH_INDEX_MAX_BYTES,
  SEARCH_INDEX_SCHEMA_VERSION,
  addGlossaryTermAnchors,
  baseKramdownId,
  glossaryTermId,
  loadAliasManifest,
  normalizeSearchText,
  pageDescriptors,
  parseMarkdownSections,
  renderSearchIndex,
  searchIndexOutputPath,
  serializeSearchIndex,
  stripInlineMarkdown,
  uniqueKramdownId,
  writeSearchIndex,
};
