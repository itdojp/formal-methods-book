#!/usr/bin/env node
'use strict';

const { execSync } = require('child_process');
const fs = require('fs');

const TOOL_LABEL_VARIANTS = [
  { tool: '【ツール準拠（そのまま動く）】', pseudo: '【擬似記法】' },
  { tool: '〖ツール準拠（そのまま動く）〗', pseudo: '〖擬似記法〗' },
];
const TOOL_LABELS = TOOL_LABEL_VARIANTS.map((v) => v.tool);
const ELLIPSIS_PATTERNS = ['...', '…'];
const ALLOY_ENGLISH_INFIX_PATTERN = /\b\w+\s+can\s+(access|read)\s+\w+\b/;
const ALLOY_ORDERING_OPEN_PATTERN = /\bopen\s+util\/ordering\s*\[/;
const ALLOY_NEXT_DEFINITION_PATTERN = /\bnext\s*[:=]/;
const ALLOY_NEXT_USAGE_PATTERN = /(\.next\b|(\^|\*)(\s*~)?\s*next\b|~\s*next\b)/;

function getPseudoLabelForToolLabel(toolLabel) {
  const variant = TOOL_LABEL_VARIANTS.find((v) => v.tool === toolLabel);
  return variant ? variant.pseudo : '【擬似記法】/〖擬似記法〗';
}

function getStandaloneToolLabel(line) {
  const trimmed = line.trim();
  return TOOL_LABELS.includes(trimmed) ? trimmed : null;
}

function findToolLabelInLine(line) {
  return TOOL_LABELS.find((label) => line.includes(label)) ?? null;
}

function getTrackedMarkdownFiles() {
  let out;
  try {
    out = execSync('git ls-files', { encoding: 'utf8' });
  } catch (err) {
    console.error(
      'Failed to list tracked files using "git ls-files". ' +
        'Make sure this script is run from within a git repository and that "git" is installed.'
    );
    if (err && err.message) {
      console.error(String(err.message));
    }
    process.exitCode = 1;
    return [];
  }
  return out
    .split(/\r?\n/)
    .filter(Boolean)
    .filter((f) => f.endsWith('.md'))
    .filter((f) => f.startsWith('src/') || f.startsWith('docs/'));
}

function reportError(filePath, lineNumber, message) {
  const safeMessage = String(message).replace(/\r?\n/g, ' ');
  console.error(`::error file=${filePath},line=${lineNumber}::${safeMessage}`);
}

function checkFile(filePath) {
  const content = fs.readFileSync(filePath, 'utf8');
  const lines = content.split(/\r?\n/);
  const errors = [];

  let sawToolLabelInFile = null;
  let toolBlockCountInFile = 0;
  for (let i = 0; i < lines.length; i++) {
    const toolLabelInLine = findToolLabelInLine(lines[i]);
    if (toolLabelInLine && sawToolLabelInFile === null) {
      sawToolLabelInFile = { line: i + 1, label: toolLabelInLine };
    }

    const standaloneToolLabel = getStandaloneToolLabel(lines[i]);

    if (toolLabelInLine && !standaloneToolLabel) {
      errors.push({
        line: i + 1,
        message: `${toolLabelInLine} は単独行で置くこと。行中利用は禁止`,
      });
      continue;
    }

    if (!standaloneToolLabel) continue;
    toolBlockCountInFile++;

    const pseudoLabel = getPseudoLabelForToolLabel(standaloneToolLabel);

    let fenceStartLine = i + 1;
    while (fenceStartLine < lines.length && lines[fenceStartLine].trim() === '') {
      fenceStartLine++;
    }

    if (fenceStartLine >= lines.length) {
      errors.push({
        line: i + 1,
        message: `${standaloneToolLabel} の直後にコードフェンスがありません（EOF）`,
      });
      continue;
    }

    if (!lines[fenceStartLine].trim().startsWith('```')) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${standaloneToolLabel} の直後はコードフェンス（\`\`\`）である必要があります`,
      });
      continue;
    }

    const fenceHeader = lines[fenceStartLine].trim();
    const fenceLang = fenceHeader.slice(3).trim().toLowerCase();

    let fenceEndLine = fenceStartLine + 1;
    let foundEnd = false;
    let ellipsisLine = null;
    let naturalLanguageQuoteLine = null;
    let alloyEnglishInfixLine = null;
    let alloyNextUsageLine = null;
    let sawAlloyOrderingOpen = false;
    let sawAlloyNextDefinition = false;
    for (; fenceEndLine < lines.length; fenceEndLine++) {
      if (lines[fenceEndLine].trim() === '```') {
        foundEnd = true;
        break;
      }

      const line = lines[fenceEndLine];

      if (
        naturalLanguageQuoteLine === null &&
        (line.includes('「') || line.includes('」'))
      ) {
        naturalLanguageQuoteLine = fenceEndLine;
      }

      if (ellipsisLine === null) {
        const hasEllipsis = ELLIPSIS_PATTERNS.some((p) => line.includes(p));
        if (hasEllipsis) ellipsisLine = fenceEndLine;
      }

      if (fenceLang === 'alloy') {
        const trimmed = line.trim();
        const isCommentLine = trimmed.startsWith('//') || trimmed.startsWith('#');
        if (!isCommentLine) {
          if (!sawAlloyOrderingOpen && ALLOY_ORDERING_OPEN_PATTERN.test(line)) {
            sawAlloyOrderingOpen = true;
          }
          if (!sawAlloyNextDefinition && ALLOY_NEXT_DEFINITION_PATTERN.test(line)) {
            sawAlloyNextDefinition = true;
          }
          if (alloyEnglishInfixLine === null && ALLOY_ENGLISH_INFIX_PATTERN.test(line)) {
            alloyEnglishInfixLine = fenceEndLine;
          }
          if (alloyNextUsageLine === null && ALLOY_NEXT_USAGE_PATTERN.test(line)) {
            alloyNextUsageLine = fenceEndLine;
          }
        }
      }
    }

    if (ellipsisLine !== null) {
      errors.push({
        line: ellipsisLine + 1,
        message: `${standaloneToolLabel} のコードブロック内に省略（.../…）があります。省略が必要なら${pseudoLabel}へ変更してください`,
      });
    }

    if (naturalLanguageQuoteLine !== null) {
      errors.push({
        line: naturalLanguageQuoteLine + 1,
        message:
          `${standaloneToolLabel} のコードブロック内に自然言語の説明（「」）が含まれています。` +
          `説明はフェンス外へ出すか、${pseudoLabel}へ変更してください`,
      });
    }

    if (alloyEnglishInfixLine !== null) {
      errors.push({
        line: alloyEnglishInfixLine + 1,
        message:
          `${standaloneToolLabel} のAlloyコードブロック内に英語風中置表現（例: "u can access e"）があります。` +
          `Alloy構文として成立しないため、式を修正するか${pseudoLabel}へ変更してください`,
      });
    }

    if (
      alloyNextUsageLine !== null &&
      !sawAlloyOrderingOpen &&
      !sawAlloyNextDefinition
    ) {
      errors.push({
        line: alloyNextUsageLine + 1,
        message:
          `${standaloneToolLabel} のAlloyコードブロック内で next（例: .next / ^next / *next / ~next）を使用していますが、` +
          '`open util/ordering[...]` も `next:` 定義も見つかりません。ブロック単体で成立するよう補ってください',
      });
    }

    if (!foundEnd) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${standaloneToolLabel} のコードブロックが閉じられていません（終了フェンス \`\`\` がありません）`,
      });
      continue;
    }

    i = fenceEndLine;
  }

  if (sawToolLabelInFile !== null && toolBlockCountInFile === 0) {
    errors.push({
      line: sawToolLabelInFile.line,
      message:
        `ツール準拠ラベル（${sawToolLabelInFile.label}）が見つかりましたが、ツールブロックとして解釈できませんでした。` +
        'ラベルは単独行で置き、直後にコードフェンス（```）を置いてください',
    });
  }

  return errors;
}

function main() {
  const files = getTrackedMarkdownFiles();
  const allErrors = [];

  for (const filePath of files) {
    const errors = checkFile(filePath);
    for (const e of errors) {
      allErrors.push({ filePath, ...e });
    }
  }

  if (allErrors.length === 0) {
    console.log('OK: tool-compliant blocks are well-formed and have no invalid patterns.');
    return;
  }

  for (const e of allErrors) {
    reportError(e.filePath, e.line, e.message);
  }

  console.error(`Found ${allErrors.length} tool block error(s).`);
  process.exitCode = 1;
}

main();
