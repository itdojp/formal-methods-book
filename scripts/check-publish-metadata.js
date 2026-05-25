#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const YAML = require('yaml');

const repoOwner = 'itdojp';
const repoName = 'formal-methods-book';
const repoFullName = `${repoOwner}/${repoName}`;
const githubUrl = `https://github.com/${repoFullName}`;
const issuesUrl = `${githubUrl}/issues`;
const pagesUrl = `https://${repoOwner}.github.io/${repoName}/`;
const siteUrl = `https://${repoOwner}.github.io`;
const baseUrl = `/${repoName}`;

const failures = [];

function fail(message) {
  failures.push(message);
}

function readText(filePath) {
  return fs.readFileSync(filePath, 'utf8');
}

function readJson(filePath) {
  try {
    return JSON.parse(readText(filePath));
  } catch (error) {
    fail(`${filePath}: JSONを解析できません: ${error.message}`);
    return {};
  }
}

function readYaml(filePath) {
  try {
    return YAML.parse(readText(filePath)) || {};
  } catch (error) {
    fail(`${filePath}: YAMLを解析できません: ${error.message}`);
    return {};
  }
}

function assertEqual(actual, expected, label) {
  if (actual !== expected) {
    fail(`${label}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function assertNoDuplicates(values, label) {
  const seen = new Set();
  const duplicates = [];
  for (const value of values) {
    if (seen.has(value) && !duplicates.includes(value)) duplicates.push(value);
    seen.add(value);
  }
  if (duplicates.length > 0) {
    fail(`${label}: duplicate entries ${JSON.stringify(duplicates)}`);
  }
}

function assertArrayEqual(actual, expected, label) {
  assertNoDuplicates(actual, `${label} actual`);
  assertNoDuplicates(expected, `${label} expected`);
  if (actual.length !== expected.length || actual.some((value, index) => value !== expected[index])) {
    fail(`${label}: expected ordered list ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

function normalizeRepositoryUrl(rawUrl) {
  if (typeof rawUrl !== 'string') return '';
  const trimmed = rawUrl.trim().replace(/\/+$/, '').replace(/\.git$/, '');
  if (trimmed === repoFullName) return githubUrl;
  try {
    const parsed = new URL(trimmed);
    const parts = parsed.pathname.split('/').filter(Boolean);
    if (parsed.hostname !== 'github.com' || parts.length !== 2) return trimmed;
    return `https://github.com/${parts[0]}/${parts[1]}`;
  } catch {
    return trimmed;
  }
}

function listContentIds(rootDir) {
  if (!fs.existsSync(rootDir)) {
    fail(`content directory not found: ${rootDir}`);
    return [];
  }
  return fs.readdirSync(rootDir, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name)
    .filter((id) => fs.existsSync(path.join(rootDir, id, 'index.md')))
    .sort();
}

function navigationIds(navigation, locale, section, prefix) {
  const entries = navigation?.[locale]?.[section] || [];
  const ids = [];
  for (const entry of entries) {
    const navPath = entry?.path;
    if (typeof navPath !== 'string' || !navPath.startsWith(prefix)) continue;
    const [, id] = navPath.slice(prefix.length).match(/^([^/]+)/) || [];
    if (id) ids.push(id);
  }
  return ids;
}

function configStructureIds(docsConfig, section) {
  const entries = docsConfig?.structure?.[section] || [];
  return entries.map((entry) => entry?.id).filter(Boolean);
}

function checkEdition({ locale, config, docsRoot, navPrefix }) {
  const chapterIds = (config.structure?.chapters || []).map((entry) => entry.id);
  const appendixIds = (config.structure?.appendices || []).map((entry) => entry.id);

  assertArrayEqual(chapterIds, listContentIds(path.join(docsRoot, 'chapters')), `${locale} book-config chapters vs publish tree`);
  assertArrayEqual(appendixIds, listContentIds(path.join(docsRoot, 'appendices')), `${locale} book-config appendices vs publish tree`);

  assertArrayEqual(
    navigationIds(navigation, locale, 'chapters', `${navPrefix}chapters/`),
    chapterIds,
    `${locale} navigation chapters vs book-config`
  );
  assertArrayEqual(
    navigationIds(navigation, locale, 'appendices', `${navPrefix}appendices/`),
    appendixIds,
    `${locale} navigation appendices vs book-config`
  );
}

const manifest = readJson('book-config.json');
const jaConfig = readJson('book-config.ja.json');
const enConfig = readJson('book-config.en.json');
const packageJson = readJson('package.json');
const packageLock = readJson('package-lock.json');
const docsConfig = readYaml('docs/_config.yml');
const navigation = readYaml('docs/_data/navigation.yml');

assertEqual(manifest.project?.id, repoName, 'book-config.json project.id');
assertEqual(manifest.project?.version, jaConfig.version, 'book-config.json project.version vs ja version');
assertEqual(manifest.project?.version, enConfig.version, 'book-config.json project.version vs en version');
assertEqual(normalizeRepositoryUrl(manifest.repository?.url), githubUrl, 'book-config.json repository.url');
assertEqual(manifest.repository?.branch, 'main', 'book-config.json repository.branch');

assertEqual(packageJson.name, repoName, 'package.json name');
assertEqual(packageJson.version, manifest.project?.version, 'package.json version');
assertEqual(normalizeRepositoryUrl(packageJson.repository?.url), githubUrl, 'package.json repository.url');
assertEqual(packageJson.homepage, pagesUrl, 'package.json homepage');
assertEqual(packageJson.bugs?.url, issuesUrl, 'package.json bugs.url');
assertEqual(packageJson.scripts?.['check:metadata'], 'node scripts/check-publish-metadata.js', 'package.json scripts.check:metadata');

assertEqual(packageLock.name, packageJson.name, 'package-lock.json name');
assertEqual(packageLock.version, packageJson.version, 'package-lock.json version');
assertEqual(packageLock.packages?.['']?.name, packageJson.name, 'package-lock root package name');
assertEqual(packageLock.packages?.['']?.version, packageJson.version, 'package-lock root package version');
assertEqual(packageLock.packages?.['']?.license, packageJson.license, 'package-lock root package license');

assertEqual(docsConfig.title, jaConfig.title, 'docs/_config.yml title');
assertEqual(docsConfig.author, jaConfig.author, 'docs/_config.yml author');
assertEqual(String(docsConfig.version), manifest.project?.version, 'docs/_config.yml version');
assertEqual(docsConfig.lang, 'ja', 'docs/_config.yml lang');
assertEqual(docsConfig.url, siteUrl, 'docs/_config.yml url');
assertEqual(docsConfig.baseurl, baseUrl, 'docs/_config.yml baseurl');
assertEqual(normalizeRepositoryUrl(docsConfig.repository), githubUrl, 'docs/_config.yml repository');

assertArrayEqual(configStructureIds(docsConfig, 'chapters'), jaConfig.structure?.chapters?.map((entry) => entry.id) || [], 'docs/_config.yml structure.chapters vs ja book-config');
assertArrayEqual(configStructureIds(docsConfig, 'appendices'), jaConfig.structure?.appendices?.map((entry) => entry.id) || [], 'docs/_config.yml structure.appendices vs ja book-config');

checkEdition({ locale: 'ja', config: jaConfig, docsRoot: 'docs', navPrefix: '/' });
checkEdition({ locale: 'en', config: enConfig, docsRoot: 'docs/en', navPrefix: '/en/' });

if (failures.length > 0) {
  console.error('Publish metadata consistency check failed:');
  for (const failure of failures) {
    console.error(`- ${failure}`);
  }
  process.exit(1);
}

console.log(`Publish metadata consistency check passed for ${repoFullName} ${manifest.project?.version}.`);
