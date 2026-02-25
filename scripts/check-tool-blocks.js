#!/usr/bin/env node
'use strict';

const { execSync } = require('child_process');
const fs = require('fs');

const TOOL_LABEL = '【ツール準拠（そのまま動く）】';
const ELLIPSIS_PATTERNS = ['...', '…'];

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

  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== TOOL_LABEL) continue;

    let fenceStartLine = i + 1;
    while (fenceStartLine < lines.length && lines[fenceStartLine].trim() === '') {
      fenceStartLine++;
    }

    if (fenceStartLine >= lines.length) {
      errors.push({
        line: i + 1,
        message: `${TOOL_LABEL} の直後にコードフェンスがありません（EOF）`,
      });
      continue;
    }

    if (!lines[fenceStartLine].trim().startsWith('```')) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${TOOL_LABEL} の直後はコードフェンス（\`\`\`）である必要があります`,
      });
      continue;
    }

    let fenceEndLine = fenceStartLine + 1;
    let foundEnd = false;
    let ellipsisLine = null;
    for (; fenceEndLine < lines.length; fenceEndLine++) {
      if (lines[fenceEndLine].trim() === '```') {
        foundEnd = true;
        break;
      }

      if (ellipsisLine === null) {
        const line = lines[fenceEndLine];
        const hasEllipsis = ELLIPSIS_PATTERNS.some((p) => line.includes(p));
        if (hasEllipsis) ellipsisLine = fenceEndLine;
      }
    }

    if (ellipsisLine !== null) {
      errors.push({
        line: ellipsisLine + 1,
        message: `${TOOL_LABEL} のコードブロック内に省略（.../…）があります。省略が必要なら【擬似記法】へ変更してください`,
      });
    }

    if (!foundEnd) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${TOOL_LABEL} のコードブロックが閉じられていません（終了フェンス \`\`\` がありません）`,
      });
      continue;
    }

    i = fenceEndLine;
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
    console.log('OK: tool-compliant blocks have no ellipsis placeholders.');
    return;
  }

  for (const e of allErrors) {
    reportError(e.filePath, e.line, e.message);
  }

  console.error(`Found ${allErrors.length} tool block error(s).`);
  process.exitCode = 1;
}

main();
