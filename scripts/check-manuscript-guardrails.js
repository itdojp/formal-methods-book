#!/usr/bin/env node
'use strict';

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

const DEFAULT_SCAN_DIR = 'docs';

const FORBIDDEN_MARKER_RULES = [
  { label: 'TBD', re: /\bTBD\b/ },
  { label: 'TODO', re: /\bTODO\b/ },
  { label: 'FIXME', re: /\bFIXME\b/ },
  { label: '執筆中', re: /執筆中/ },
  { label: '準備中', re: /準備中/ },
  { label: '未作成', re: /未作成/ },
];

function escapeRegExp(input) {
  return String(input).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function getTrackedFiles() {
  try {
    return execSync('git ls-files', { encoding: 'utf8' })
      .split(/\r?\n/)
      .filter(Boolean);
  } catch (err) {
    console.error('Failed to list tracked files using "git ls-files".');
    if (err && err.message) console.error(String(err.message));
    process.exitCode = 1;
    return [];
  }
}

function reportError(filePath, lineNumber, message) {
  const safeMessage = String(message).replace(/\r?\n/g, ' ');
  console.error(`::error file=${filePath},line=${lineNumber}::${safeMessage}`);
}

function normalizeScanDir(scanDirRaw) {
  const scanDir = String(scanDirRaw || DEFAULT_SCAN_DIR).trim() || DEFAULT_SCAN_DIR;
  if (scanDir === '.') return '.';
  return scanDir.replace(/\/+$/, '');
}

function checkForbiddenMarkers(markdownFiles) {
  const errors = [];

  for (const filePath of markdownFiles) {
    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      for (const rule of FORBIDDEN_MARKER_RULES) {
        if (!rule.re.test(line)) continue;
        errors.push({
          filePath,
          line: i + 1,
          message: `残骸マーカー検出: ${rule.label}（除去または表現変更してください）`,
        });
      }
    }
  }

  return errors;
}

function checkChapterEndings(chapterFiles) {
  const errors = [];
  const numberedSectionHeadingRe = /^##\s+\d+\.\d+\b/;

  for (const filePath of chapterFiles) {
    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);

    let chapterEndIndex = -1;
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].trim() === '## 章末課題') {
        chapterEndIndex = i;
        break;
      }
    }

    if (chapterEndIndex === -1) {
      errors.push({
        filePath,
        line: 1,
        message: '章末課題の見出し（## 章末課題）が見つかりません（見出し名の統一、または章末課題の追加が必要です）',
      });
      continue;
    }

    for (let i = chapterEndIndex + 1; i < lines.length; i++) {
      if (lines[i].trim() === '## 章末課題') {
        errors.push({
          filePath,
          line: i + 1,
          message: '章末課題の見出し（## 章末課題）が複数回出現しています（1つに統一してください）',
        });
        break;
      }
    }

    for (let i = chapterEndIndex + 1; i < lines.length; i++) {
      if (!numberedSectionHeadingRe.test(lines[i])) continue;
      errors.push({
        filePath,
        line: i + 1,
        message: '章末課題（## 章末課題）の後に本文セクション見出し（## x.y）が出現しています（章末課題は章末に集約してください）',
      });
      break;
    }
  }

  return errors;
}

function main() {
  const scanDir = normalizeScanDir(process.argv[2]);
  const prefix = scanDir === '.' ? '' : `${scanDir}/`;

  const tracked = getTrackedFiles();
  const markdownFiles = tracked.filter((f) => f.endsWith('.md') && f.startsWith(prefix));

  const chaptersPattern = new RegExp(
    `^${escapeRegExp(prefix)}chapters\\/chapter\\d+\\/index\\.md$`
  );
  const chapterFiles = markdownFiles.filter((f) => chaptersPattern.test(f));

  const allErrors = [
    ...checkForbiddenMarkers(markdownFiles),
    ...checkChapterEndings(chapterFiles),
  ];

  if (allErrors.length === 0) {
    console.log('OK: manuscript guardrails passed (chapter endings + forbidden markers).');
    return;
  }

  for (const e of allErrors) {
    reportError(e.filePath, e.line, e.message);
  }

  console.error(`Found ${allErrors.length} guardrail violation(s).`);
  process.exitCode = 1;
}

main();

