'use strict';

const fs = require('fs');
const path = require('path');
const { resolveSourcePage } = require('./publication-metadata');
const {
  insertTranslationNotice,
  loadTranslationManifest,
  validateTranslationManifest,
} = require('./translation-status');

function toPosix(filePath) {
  return filePath.split(path.sep).join('/');
}

function ensureDir(dirPath) {
  fs.mkdirSync(dirPath, { recursive: true });
}

function assertNoSymlinkComponents(repoRoot, targetPath, label) {
  const root = path.resolve(repoRoot);
  const target = path.resolve(targetPath);
  if (target !== root && !target.startsWith(`${root}${path.sep}`)) {
    throw new Error(`${label}: path escapes repository root`);
  }
  let current = root;
  const relativePath = path.relative(root, target);
  for (const segment of relativePath.split(path.sep).filter(Boolean)) {
    current = path.join(current, segment);
    const entry = fs.lstatSync(current, { throwIfNoEntry: false });
    if (entry?.isSymbolicLink()) {
      throw new Error(`${label}: symbolic link path component is not allowed: ${toPosix(path.relative(root, current))}`);
    }
  }
}

function escapeYaml(value) {
  return String(value || '').replace(/\\/g, '\\\\').replace(/"/g, '\\"');
}

function readMarkdownTitle(content, fallback) {
  const match = content.match(/^#\s+(.+)$/m);
  return match ? match[1].trim() : fallback;
}

function rewriteExampleLinksForPublication(content) {
  const revision = "{{site.github.build_revision|default:'main'}}";
  return content.replace(
    /\[(examples\/[A-Za-z0-9_./-]+)\]\([^)]+\)/g,
    (_, repositoryPath) =>
      `[${repositoryPath}](https://github.com/itdojp/formal-methods-book/blob/${revision}/${repositoryPath})`,
  );
}

function rewriteAssetLinksForPublication(content, { repoRoot, outputFile }) {
  return content.replace(/(?:\.\.\/)+docs\/assets\/[A-Za-z0-9_./-]+/g, (sourceLink) => {
    const target = path.resolve(repoRoot, sourceLink.replace(/^(?:\.\.\/)+/, ''));
    const assetsRoot = path.resolve(repoRoot, 'docs', 'assets');
    if (target !== assetsRoot && !target.startsWith(`${assetsRoot}${path.sep}`)) {
      return sourceLink;
    }
    return toPosix(path.relative(path.dirname(outputFile), target));
  });
}

function wrapWithFrontMatter({ title, description, locale, sourcePath, translationStatus }, content) {
  const lines = [
    '---',
    'layout: book',
    `title: "${escapeYaml(title)}"`,
    ...(description ? [`description: "${escapeYaml(description)}"`] : []),
    `locale: "${locale}"`,
    `lang: "${locale}"`,
    `source_path: "${sourcePath}"`,
    ...(translationStatus ? [
      `translation_status: "${translationStatus.status}"`,
      `translation_source_commit: "${translationStatus.source_commit}"`,
      `translation_reviewed_at: "${translationStatus.reviewed_at}"`,
      ...(translationStatus.tracking_issue
        ? [`translation_tracking_issue: "${escapeYaml(translationStatus.tracking_issue)}"`]
        : []),
    ] : []),
    '---',
    '',
  ];
  return `${lines.join('\n')}${content.trimEnd()}\n`;
}

function shouldBuildFile(relativePath) {
  return toPosix(relativePath) !== 'appendices/appendices_draft.md';
}

function collectSourceFiles(sourceRoot) {
  const files = [];
  function walk(dirPath) {
    for (const entry of fs.readdirSync(dirPath, { withFileTypes: true })) {
      const absolutePath = path.join(dirPath, entry.name);
      if (entry.isDirectory()) {
        walk(absolutePath);
      } else if (entry.isFile() && entry.name.endsWith('.md')) {
        files.push(absolutePath);
      }
    }
  }
  walk(sourceRoot);
  return files.sort();
}

function renderPublicationPage({
  content,
  locale,
  metadata,
  outputFile,
  repoRoot,
  sourcePath,
  translationStatus,
}) {
  let rendered = translationStatus ? insertTranslationNotice(content, translationStatus) : content;
  rendered = rewriteExampleLinksForPublication(rendered);
  rendered = rewriteAssetLinksForPublication(rendered, { repoRoot, outputFile });
  const title = metadata?.title || readMarkdownTitle(rendered, path.basename(sourcePath, '.md'));
  return wrapWithFrontMatter({
    title,
    description: metadata?.description,
    locale,
    sourcePath,
    translationStatus,
  }, rendered);
}

function renderEditionPages(repoRoot, model, locale) {
  const manifestEdition = model.manifest.editions?.[locale];
  const config = model.editions?.[locale];
  if (!manifestEdition || !config) {
    throw new Error(`Edition config not found: ${locale}`);
  }

  const sourceRoot = path.join(repoRoot, manifestEdition.sourceRoot);
  assertNoSymlinkComponents(repoRoot, sourceRoot, `${locale} source root`);
  if (!fs.existsSync(sourceRoot)) {
    throw new Error(`Source root not found: ${manifestEdition.sourceRoot}`);
  }

  let translationManifest = null;
  if (manifestEdition.translationOf) {
    translationManifest = loadTranslationManifest(repoRoot, model);
    const translationErrors = validateTranslationManifest(translationManifest, model);
    if (translationErrors.length > 0) {
      throw new Error(`Invalid translation status manifest:\n- ${translationErrors.join('\n- ')}`);
    }
    if (translationManifest.translation_locale !== locale) {
      throw new Error(`Translation status manifest does not describe edition: ${locale}`);
    }
  }

  const pages = new Map();
  for (const sourceFile of collectSourceFiles(sourceRoot)) {
    const relativePath = path.relative(sourceRoot, sourceFile);
    if (!shouldBuildFile(relativePath)) continue;
    const page = resolveSourcePage(config, relativePath);
    if (!page) {
      throw new Error(`${locale}: source file has no publication mapping: ${toPosix(relativePath)}`);
    }

    const outputPath = toPosix(path.join(manifestEdition.publishRoot, ...page.outputSegments));
    if (pages.has(outputPath)) {
      throw new Error(`${locale}: duplicate publication output ${outputPath}`);
    }
    const outputFile = path.join(repoRoot, outputPath);
    const sourcePath = toPosix(path.join(manifestEdition.sourceRoot, relativePath));
    const translationStatus = translationManifest?.pages[toPosix(relativePath)];
    if (translationManifest && !translationStatus) {
      throw new Error(`${locale}: translation status is missing for ${toPosix(relativePath)}`);
    }
    pages.set(outputPath, renderPublicationPage({
      content: fs.readFileSync(sourceFile, 'utf8'),
      locale,
      metadata: page.metadata,
      outputFile,
      repoRoot,
      sourcePath,
      translationStatus,
    }));
  }
  const expectedPageCount = 1
    + (config.structure?.chapters || []).length
    + (config.structure?.appendices || []).length
    + (config.structure?.specialPages || []).length;
  if (pages.size !== expectedPageCount) {
    throw new Error(`${locale}: expected ${expectedPageCount} declared publication pages, rendered ${pages.size}`);
  }
  return pages;
}

function sourcePathFromFrontMatter(content) {
  const frontMatter = content.match(/^---\r?\n([\s\S]*?)\r?\n---\r?\n/);
  if (!frontMatter) return null;
  const sourcePath = frontMatter[1].match(/^source_path:\s*["']?([^"'\r\n]+)["']?\s*$/m);
  return sourcePath ? sourcePath[1].trim() : null;
}

function nestedPublishRoots(repoRoot, model, locale) {
  const currentRoot = path.resolve(repoRoot, model.manifest.editions[locale].publishRoot);
  return Object.entries(model.manifest.editions)
    .filter(([candidate]) => candidate !== locale)
    .map(([, edition]) => path.resolve(repoRoot, edition.publishRoot))
    .filter((candidateRoot) => candidateRoot.startsWith(`${currentRoot}${path.sep}`));
}

function collectStaleGeneratedPages(repoRoot, model, locale, expectedPaths) {
  const edition = model.manifest.editions[locale];
  const publishRoot = path.resolve(repoRoot, edition.publishRoot);
  assertNoSymlinkComponents(repoRoot, publishRoot, `${locale} publish root`);
  if (!fs.existsSync(publishRoot)) return [];
  const excludedRoots = nestedPublishRoots(repoRoot, model, locale);
  const stale = [];

  function walk(dirPath) {
    if (excludedRoots.includes(path.resolve(dirPath))) return;
    for (const entry of fs.readdirSync(dirPath, { withFileTypes: true })) {
      const absolutePath = path.join(dirPath, entry.name);
      if (entry.isDirectory()) {
        walk(absolutePath);
        continue;
      }
      if (!entry.isFile() || !entry.name.endsWith('.md')) continue;
      const relativePath = toPosix(path.relative(repoRoot, absolutePath));
      if (expectedPaths.has(relativePath)) continue;
      const sourcePath = sourcePathFromFrontMatter(fs.readFileSync(absolutePath, 'utf8'));
      if (sourcePath?.startsWith(`${edition.sourceRoot}/`)) stale.push(relativePath);
    }
  }

  walk(publishRoot);
  return stale.sort();
}

function removeEmptyParents(filePath, stopDir) {
  let current = path.dirname(filePath);
  const boundary = path.resolve(stopDir);
  while (current !== boundary && current.startsWith(`${boundary}${path.sep}`)) {
    if (fs.readdirSync(current).length > 0) break;
    fs.rmdirSync(current);
    current = path.dirname(current);
  }
}

function writeEditionPages(repoRoot, model, locale, pages) {
  const expectedPaths = new Set(pages.keys());
  const publishRoot = path.join(repoRoot, model.manifest.editions[locale].publishRoot);
  for (const stalePath of collectStaleGeneratedPages(repoRoot, model, locale, expectedPaths)) {
    const staleFile = path.join(repoRoot, stalePath);
    fs.rmSync(staleFile, { force: true });
    removeEmptyParents(staleFile, publishRoot);
  }
  for (const [relativePath, content] of pages) {
    const outputFile = path.join(repoRoot, relativePath);
    assertNoSymlinkComponents(repoRoot, outputFile, `${locale} publication output ${relativePath}`);
    ensureDir(path.dirname(outputFile));
    fs.writeFileSync(outputFile, content);
  }
}

function compareEditionPages(repoRoot, model, locale, pages) {
  const differences = [];
  for (const [relativePath, expected] of pages) {
    const outputFile = path.join(repoRoot, relativePath);
    assertNoSymlinkComponents(repoRoot, outputFile, `${locale} publication output ${relativePath}`);
    if (!fs.existsSync(outputFile)) {
      differences.push(`${relativePath}: missing generated publication page`);
      continue;
    }
    if (fs.readFileSync(outputFile, 'utf8') !== expected) {
      differences.push(`${relativePath}: stale or manually edited generated publication page`);
    }
  }
  const expectedPaths = new Set(pages.keys());
  for (const stalePath of collectStaleGeneratedPages(repoRoot, model, locale, expectedPaths)) {
    differences.push(`${stalePath}: unexpected generated publication page`);
  }
  return differences.sort();
}

module.exports = {
  assertNoSymlinkComponents,
  collectSourceFiles,
  collectStaleGeneratedPages,
  compareEditionPages,
  renderEditionPages,
  renderPublicationPage,
  rewriteAssetLinksForPublication,
  rewriteExampleLinksForPublication,
  sourcePathFromFrontMatter,
  wrapWithFrontMatter,
  writeEditionPages,
};
