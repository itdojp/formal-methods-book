#!/usr/bin/env node
'use strict';

const { execSync } = require('child_process');
const fs = require('fs');

const CODE_LABEL_VARIANTS = [
  {
    kind: 'tool',
    label: '【ツール準拠（そのまま動く）】',
    pseudo: '【擬似記法】',
  },
  {
    kind: 'tool',
    label: '〖ツール準拠（そのまま動く）〗',
    pseudo: '〖擬似記法〗',
  },
  {
    kind: 'context',
    label: '【文脈依存スニペット】',
    pseudo: '【擬似記法】',
  },
  {
    kind: 'context',
    label: '〖文脈依存スニペット〗',
    pseudo: '〖擬似記法〗',
  },
];
const CODE_LABELS = CODE_LABEL_VARIANTS.map((v) => v.label);
const ELLIPSIS_PATTERNS = ['...', '…'];
const ALLOY_ENGLISH_INFIX_PATTERN = /\b\w+\s+can\s+(access|read)\s+\w+\b/;
const ALLOY_ORDERING_OPEN_PATTERN = /\bopen\s+util\/ordering\s*\[/;
const ALLOY_NEXT_DEFINITION_PATTERN = /\bnext\s*[:=]/;
const ALLOY_NEXT_USAGE_PATTERN = /(\.next\b|(\^|\*)(\s*~)?\s*next\b|~\s*next\b)/;

function getLabelVariant(label) {
  return CODE_LABEL_VARIANTS.find((v) => v.label === label) ?? null;
}

function getPseudoLabelForCodeLabel(label) {
  const variant = getLabelVariant(label);
  return variant ? variant.pseudo : '【擬似記法】/〖擬似記法〗';
}

function getStandaloneCodeLabel(line) {
  const trimmed = line.trim();
  return CODE_LABELS.includes(trimmed) ? trimmed : null;
}

function findCodeLabelInLine(line) {
  return CODE_LABELS.find((label) => line.includes(label)) ?? null;
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

  let sawCodeLabelInFile = null;
  let codeBlockCountInFile = 0;
  for (let i = 0; i < lines.length; i++) {
    const codeLabelInLine = findCodeLabelInLine(lines[i]);
    if (codeLabelInLine && sawCodeLabelInFile === null) {
      sawCodeLabelInFile = { line: i + 1, label: codeLabelInLine };
    }

    const standaloneCodeLabel = getStandaloneCodeLabel(lines[i]);

    if (codeLabelInLine && !standaloneCodeLabel) {
      errors.push({
        line: i + 1,
        message: `${codeLabelInLine} は単独行で置くこと。行中利用は禁止`,
      });
      continue;
    }

    if (!standaloneCodeLabel) continue;
    codeBlockCountInFile++;

    const pseudoLabel = getPseudoLabelForCodeLabel(standaloneCodeLabel);
    const labelVariant = getLabelVariant(standaloneCodeLabel);
    const isStrictToolLabel = labelVariant && labelVariant.kind === 'tool';

    let fenceStartLine = i + 1;
    while (fenceStartLine < lines.length && lines[fenceStartLine].trim() === '') {
      fenceStartLine++;
    }

    if (fenceStartLine >= lines.length) {
      errors.push({
        line: i + 1,
        message: `${standaloneCodeLabel} の直後にコードフェンスがありません（EOF）`,
      });
      continue;
    }

    if (!lines[fenceStartLine].trim().startsWith('```')) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${standaloneCodeLabel} の直後はコードフェンス（\`\`\`）である必要があります`,
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
        message: `${standaloneCodeLabel} のコードブロック内に省略（.../…）があります。省略が必要なら${pseudoLabel}へ変更してください`,
      });
    }

    if (naturalLanguageQuoteLine !== null) {
      errors.push({
        line: naturalLanguageQuoteLine + 1,
        message:
          `${standaloneCodeLabel} のコードブロック内に自然言語の説明（「」）が含まれています。` +
          `説明はフェンス外へ出すか、${pseudoLabel}へ変更してください`,
      });
    }

    if (alloyEnglishInfixLine !== null) {
      errors.push({
        line: alloyEnglishInfixLine + 1,
        message:
          `${standaloneCodeLabel} のAlloyコードブロック内に英語風中置表現（例: "u can access e"）があります。` +
          `Alloy構文として成立しないため、式を修正するか${pseudoLabel}へ変更してください`,
      });
    }

    if (
      isStrictToolLabel &&
      alloyNextUsageLine !== null &&
      !sawAlloyOrderingOpen &&
      !sawAlloyNextDefinition
    ) {
      errors.push({
        line: alloyNextUsageLine + 1,
        message:
          `${standaloneCodeLabel} のAlloyコードブロック内で next（例: .next / ^next / *next / ~next）を使用していますが、` +
          '`open util/ordering[...]` も `next:` 定義も見つかりません。ブロック単体で成立するよう補ってください',
      });
    }

    if (!foundEnd) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${standaloneCodeLabel} のコードブロックが閉じられていません（終了フェンス \`\`\` がありません）`,
      });
      continue;
    }

    i = fenceEndLine;
  }

  if (sawCodeLabelInFile !== null && codeBlockCountInFile === 0) {
    errors.push({
      line: sawCodeLabelInFile.line,
      message:
        `コードラベル（${sawCodeLabelInFile.label}）が見つかりましたが、コードブロックとして解釈できませんでした。` +
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
