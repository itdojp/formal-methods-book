#!/usr/bin/env node
'use strict';

const { execSync } = require('child_process');
const fs = require('fs');

const DEFAULT_SCAN_DIR = 'docs';

const FORBIDDEN_MARKER_RULES = [
  { label: 'TBD', re: /\bTBD\b/ },
  { label: 'TODO', re: /\bTODO\b/ },
  { label: 'FIXME', re: /\bFIXME\b/ },
  { label: '執筆中', re: /執筆中/ },
  { label: '準備中', re: /準備中/ },
  { label: '未作成', re: /未作成/ },
];

const FIGURE_LABEL_PATTERN = /図\s*(\d+)\s*[-‐‑‒–—―−]\s*(\d+)/g;
const MARKDOWN_IMAGE_PATTERN = /!\[([^\]]*?)\]\([^)]+\)/g;
const MINI_SUMMARY_HEADING = 'ミニ要約：';
const REFERENCE_SECTION_KEYWORD = '図・章参照';
const LIST_ITEM_PATTERN = /^\s*[-*]\s+/;
const LEVEL2_HEADING_PATTERN = /^##\s+/;
const MINI_SUMMARY_BARE_FIGURE_SUFFIX_PATTERN =
  /[\/／,，、・]\s*(\d{1,2})\s*[-‐‑‒–—―−]\s*(\d{1,2})/g;

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

function checkChapterNumbering(chapterFiles) {
  const errors = [];
  const chapterNumberFromPathRe = /chapter(\d+)\//;
  const numberedSectionHeadingRe = /^##\s+(\d+)\.(\d+)\b/;

  for (const filePath of chapterFiles) {
    const chapterMatch = filePath.match(chapterNumberFromPathRe);
    const expectedChapterNumber = chapterMatch ? parseInt(chapterMatch[1], 10) : null;

    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);

    const seen = new Map();
    let prevMinor = null;
    let firstMinor = null;

    for (let i = 0; i < lines.length; i++) {
      const match = lines[i].match(numberedSectionHeadingRe);
      if (!match) continue;

      const major = parseInt(match[1], 10);
      const minor = parseInt(match[2], 10);

      if (expectedChapterNumber !== null && major !== expectedChapterNumber) {
        errors.push({
          filePath,
          line: i + 1,
          message: `見出し番号の章番号がファイル名と一致しません（期待: ${expectedChapterNumber}.x / 実際: ${major}.${minor}）`,
        });
      }

      const key = `${major}.${minor}`;
      if (seen.has(key)) {
        errors.push({
          filePath,
          line: i + 1,
          message: `見出し番号が重複しています: ${key}（前回: L${seen.get(key)}）`,
        });
      } else {
        seen.set(key, i + 1);
      }

      if (firstMinor === null) {
        firstMinor = minor;
      }

      if (prevMinor !== null) {
        if (minor < prevMinor) {
          errors.push({
            filePath,
            line: i + 1,
            message: `見出し番号が逆行しています: ${major}.${prevMinor} → ${key}`,
          });
        } else if (minor > prevMinor + 1) {
          errors.push({
            filePath,
            line: i + 1,
            message: `見出し番号が飛んでいます: ${major}.${prevMinor} → ${key}`,
          });
        }
      }

      prevMinor = minor;
    }

    if (firstMinor !== null && firstMinor !== 1) {
      errors.push({
        filePath,
        line: 1,
        message: `最初の節番号が 1 ではありません（期待: ${expectedChapterNumber || '章番号'}.1 / 実際: ${expectedChapterNumber || '章番号'}.${firstMinor}）`,
      });
    }
  }

  return errors;
}

function collectDefinedFigures(markdownFiles) {
  const defined = new Map();

  for (const filePath of markdownFiles) {
    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      for (const imageMatch of line.matchAll(new RegExp(MARKDOWN_IMAGE_PATTERN))) {
        const alt = imageMatch[1] || '';
        for (const figureMatch of alt.matchAll(new RegExp(FIGURE_LABEL_PATTERN))) {
          const label = `図${parseInt(figureMatch[1], 10)}-${parseInt(figureMatch[2], 10)}`;
          if (defined.has(label)) continue;
          defined.set(label, { filePath, line: i + 1 });
        }
      }
    }
  }

  return defined;
}

function checkFigureReferences(markdownFiles, definedFigures) {
  const errors = [];

  for (const filePath of markdownFiles) {
    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);

    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      for (const match of line.matchAll(new RegExp(FIGURE_LABEL_PATTERN))) {
        const label = `図${parseInt(match[1], 10)}-${parseInt(match[2], 10)}`;
        if (definedFigures.has(label)) continue;
        errors.push({
          filePath,
          line: i + 1,
          message: `図参照が定義されていません: ${label}（画像キャプション等の定義を確認してください）`,
        });
      }
    }
  }

  return errors;
}

function findMiniSummaryRange(lines) {
  let headingIndex = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() === MINI_SUMMARY_HEADING) {
      headingIndex = i;
      break;
    }
  }
  if (headingIndex === -1) return null;

  let startIndex = headingIndex + 1;
  while (startIndex < lines.length && lines[startIndex].trim() === '') {
    startIndex++;
  }

  let endIndex = startIndex;
  while (endIndex < lines.length && LIST_ITEM_PATTERN.test(lines[endIndex])) {
    endIndex++;
  }

  if (endIndex === startIndex) return null;

  return {
    headingLine: headingIndex + 1,
    startIndex,
    endIndex,
  };
}

function findLevel2SectionRange(lines, keyword) {
  let headingIndex = -1;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!LEVEL2_HEADING_PATTERN.test(line)) continue;
    if (!line.includes(keyword)) continue;
    headingIndex = i;
    break;
  }
  if (headingIndex === -1) return null;

  let endIndex = lines.length;
  for (let i = headingIndex + 1; i < lines.length; i++) {
    if (!LEVEL2_HEADING_PATTERN.test(lines[i].trim())) continue;
    endIndex = i;
    break;
  }

  return {
    headingLine: headingIndex + 1,
    startIndex: headingIndex + 1,
    endIndex,
  };
}

function collectFigureReferencesInRange(lines, startIndex, endIndex) {
  const refs = new Map();
  for (let i = startIndex; i < endIndex; i++) {
    const line = lines[i];
    for (const match of line.matchAll(new RegExp(FIGURE_LABEL_PATTERN))) {
      const label = `図${parseInt(match[1], 10)}-${parseInt(match[2], 10)}`;
      if (!refs.has(label)) refs.set(label, []);
      refs.get(label).push(i + 1);
    }
  }
  return refs;
}

function hasFigureReference(line) {
  for (const _ of line.matchAll(new RegExp(FIGURE_LABEL_PATTERN))) {
    return true;
  }
  return false;
}

function checkMiniSummaryFigureConsistency(chapterFiles) {
  const errors = [];

  for (const filePath of chapterFiles) {
    const content = fs.readFileSync(filePath, 'utf8');
    const lines = content.split(/\r?\n/);

    const mini = findMiniSummaryRange(lines);
    if (!mini) continue;

    const references = findLevel2SectionRange(lines, REFERENCE_SECTION_KEYWORD);
    if (!references) continue;

    for (let i = mini.startIndex; i < mini.endIndex; i++) {
      const line = lines[i];
      if (!hasFigureReference(line)) continue;

      for (const match of line.matchAll(new RegExp(MINI_SUMMARY_BARE_FIGURE_SUFFIX_PATTERN))) {
        const label = `図${parseInt(match[1], 10)}-${parseInt(match[2], 10)}`;
        errors.push({
          filePath,
          line: i + 1,
          message: `ミニ要約内の図番号は「図」を省略せず記載してください: ${label}`,
        });
      }
    }

    const miniRefs = collectFigureReferencesInRange(lines, mini.startIndex, mini.endIndex);
    const refRefs = collectFigureReferencesInRange(
      lines,
      references.startIndex,
      references.endIndex
    );

    const miniSet = new Set(miniRefs.keys());
    const refSet = new Set(refRefs.keys());

    for (const label of miniSet) {
      if (refSet.has(label)) continue;
      const firstLine = miniRefs.get(label)[0] || mini.headingLine;
      errors.push({
        filePath,
        line: firstLine,
        message: `ミニ要約の図参照が「${REFERENCE_SECTION_KEYWORD}」節にありません: ${label}（節: L${references.headingLine}）`,
      });
    }

    for (const label of refSet) {
      if (miniSet.has(label)) continue;
      const firstLine = refRefs.get(label)[0] || references.headingLine;
      errors.push({
        filePath,
        line: firstLine,
        message: `「${REFERENCE_SECTION_KEYWORD}」節の図参照がミニ要約にありません: ${label}（ミニ要約: L${mini.headingLine}）`,
      });
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

  const definedFigures = collectDefinedFigures(markdownFiles);

  const allErrors = [
    ...checkForbiddenMarkers(markdownFiles),
    ...checkChapterEndings(chapterFiles),
    ...checkChapterNumbering(chapterFiles),
    ...checkFigureReferences(markdownFiles, definedFigures),
    ...checkMiniSummaryFigureConsistency(chapterFiles),
  ];

  if (allErrors.length === 0) {
    console.log(
      'OK: manuscript guardrails passed (chapter endings + forbidden markers + numbering + figure refs + mini summary refs).'
    );
    return;
  }

  for (const e of allErrors) {
    reportError(e.filePath, e.line, e.message);
  }

  console.error(`Found ${allErrors.length} guardrail violation(s).`);
  process.exitCode = 1;
}

main();
