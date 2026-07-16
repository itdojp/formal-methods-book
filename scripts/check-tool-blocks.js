#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { loadManifest, runnerCommand } = require('./example-manifest');

const CODE_LABEL_VARIANTS = [
  {
    kind: 'tool',
    label: '【ツール準拠（そのまま動く）】',
    pseudo: '【擬似記法】',
    context: '【文脈依存スニペット】',
  },
  {
    kind: 'tool',
    label: '〖ツール準拠（そのまま動く）〗',
    pseudo: '〖擬似記法〗',
    context: '〖文脈依存スニペット〗',
  },
  {
    kind: 'tool',
    label: '【Tool-compliant (runs as-is)】',
    pseudo: '【Pseudo notation】',
    context: '【Context-dependent snippet】',
  },
  {
    kind: 'tool',
    label: '〖Tool-compliant (runs as-is)〗',
    pseudo: '〖Pseudo notation〗',
    context: '〖Context-dependent snippet〗',
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
  {
    kind: 'context',
    label: '【Context-dependent snippet】',
    pseudo: '【Pseudo notation】',
  },
  {
    kind: 'context',
    label: '〖Context-dependent snippet〗',
    pseudo: '〖Pseudo notation〗',
  },
];
const CODE_LABELS = CODE_LABEL_VARIANTS.map((v) => v.label);
const ELLIPSIS_PATTERNS = ['...', '…'];
const ALLOY_ENGLISH_INFIX_PATTERN = /\b\w+\s+can\s+(access|read)\s+\w+\b/;
const ALLOY_ORDERING_OPEN_PATTERN = /\bopen\s+util\/ordering\s*\[/;
const ALLOY_NEXT_DEFINITION_PATTERN = /\bnext\s*[:=]/;
const ALLOY_NEXT_USAGE_PATTERN = /(\.next\b|(\^|\*)(\s*~)?\s*next\b|~\s*next\b)/;
const STRICT_TOOL_DISALLOWED_FENCE_LANGS = new Set(['', 'text', 'plaintext']);
const ALLOY_BOOLEAN_TYPE_PATTERN = /\bBoolean\b/;
const ALLOY_BOOLEAN_LITERAL_PATTERN = /\b(True|False)\b/;
const ALLOY_BOOLEAN_OPEN_PATTERN = /\bopen\s+util\/boolean\b/;
const ALLOY_BOOL_TYPE_PATTERN = /\bBool\b/;
const IGNORED_DIR_NAMES = new Set([
  '.git',
  'node_modules',
  '_site',
  '.jekyll-cache',
  '.sass-cache',
]);

function getLabelVariant(label) {
  return CODE_LABEL_VARIANTS.find((v) => v.label === label) ?? null;
}

function getPseudoLabelForCodeLabel(label) {
  const variant = getLabelVariant(label);
  return variant ? variant.pseudo : '【擬似記法】/〖擬似記法〗';
}

function getContextLabelForCodeLabel(label) {
  const variant = getLabelVariant(label);
  if (variant?.context) return variant.context;
  if (label.startsWith('〖')) return '〖文脈依存スニペット〗';
  return '【文脈依存スニペット】';
}

function getStandaloneCodeLabel(line) {
  const trimmed = line.trim();
  return CODE_LABELS.includes(trimmed) ? trimmed : null;
}

function findCodeLabelInLine(line) {
  return CODE_LABELS.find((label) => line.includes(label)) ?? null;
}

function getTrackedMarkdownFiles() {
  function collectMarkdownFiles(rootDir) {
    const filePaths = [];
    const entries = fs.readdirSync(rootDir, { withFileTypes: true });

    for (const entry of entries) {
      const entryPath = path.join(rootDir, entry.name);
      if (entry.isDirectory()) {
        if (IGNORED_DIR_NAMES.has(entry.name)) {
          continue;
        }
        filePaths.push(...collectMarkdownFiles(entryPath));
        continue;
      }
      if (entry.isFile() && entryPath.endsWith('.md')) {
        filePaths.push(path.relative(process.cwd(), entryPath).split(path.sep).join('/'));
      }
    }

    return filePaths;
  }

  return ['src', 'docs']
    .filter((rootDir) => fs.existsSync(rootDir))
    .flatMap((rootDir) => collectMarkdownFiles(rootDir))
    .sort();
}

function reportError(filePath, lineNumber, message) {
  const safeMessage = String(message).replace(/\r?\n/g, ' ');
  console.error(`::error file=${filePath},line=${lineNumber}::${safeMessage}`);
}

function checkFile(filePath, manifestIds) {
  const content = fs.readFileSync(filePath, 'utf8');
  const lines = content.split(/\r?\n/);
  const errors = [];
  const registrationsInFile = new Map();

  let sawCodeLabelInFile = null;
  let codeBlockCountInFile = 0;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].includes('example-contract:')) {
      const registrationMatch = lines[i].trim().match(
        /^<!-- example-contract: ([a-z0-9]+(?:-[a-z0-9]+)*) -->$/,
      );
      if (!registrationMatch) {
        errors.push({
          line: i + 1,
          message: 'example contract comment は <!-- example-contract: ID --> の完全一致形式で記述してください',
        });
      } else {
        const registrationId = registrationMatch[1];
        const previousLine = registrationsInFile.get(registrationId);
        if (previousLine) {
          errors.push({
            line: i + 1,
            message: `example contract ID が同じファイル内で重複しています: ${registrationId} (first line ${previousLine})`,
          });
        } else {
          registrationsInFile.set(registrationId, i + 1);
        }
        const nextLabel = i + 1 < lines.length ? getStandaloneCodeLabel(lines[i + 1]) : null;
        const nextVariant = nextLabel ? getLabelVariant(nextLabel) : null;
        if (!nextVariant || nextVariant.kind !== 'tool') {
          errors.push({
            line: i + 1,
            message: `example contract ${registrationId} の直後に strict tool label がありません`,
          });
        }
        if (!manifestIds.has(registrationId)) {
          errors.push({
            line: i + 1,
            message: `example contract ID が manifest に存在しません: ${registrationId}`,
          });
        }
      }
    }

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
    let registrationId = null;
    if (isStrictToolLabel) {
      const previousLine = i > 0 ? lines[i - 1].trim() : '';
      const registrationMatch = previousLine.match(
        /^<!-- example-contract: ([a-z0-9]+(?:-[a-z0-9]+)*) -->$/,
      );
      if (!registrationMatch) {
        errors.push({
          line: i + 1,
          message:
            `${standaloneCodeLabel} の直前に <!-- example-contract: ID --> がありません。` +
            'strict label は manifest entry に必ず登録してください',
        });
      } else {
        registrationId = registrationMatch[1];
        if (!manifestIds.has(registrationId)) {
          errors.push({
            line: i,
            message: `example contract ID が manifest に存在しません: ${registrationId}`,
          });
        }
      }
    }

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

    if (isStrictToolLabel && fenceLang !== 'bash') {
      errors.push({
        line: fenceStartLine + 1,
        message:
          `${standaloneCodeLabel} の登録済み実行契約は bash fence である必要があります。` +
          '実体コードは examples/** に置き、manifest runner を呼び出してください',
      });
    }

    if (isStrictToolLabel && STRICT_TOOL_DISALLOWED_FENCE_LANGS.has(fenceLang)) {
      const contextLabel = getContextLabelForCodeLabel(standaloneCodeLabel);
      errors.push({
        line: fenceStartLine + 1,
        message:
          `${standaloneCodeLabel} のコードフェンス言語が ${fenceLang || '(未指定)'} です。` +
          '実行可能な入力なら実言語（alloy/smv/promela/...）を指定し、' +
          `説明用断片なら${contextLabel}または${pseudoLabel}へ変更してください`,
      });
    }

    let fenceEndLine = fenceStartLine + 1;
    let foundEnd = false;
    let ellipsisLine = null;
    let naturalLanguageQuoteLine = null;
    let alloyEnglishInfixLine = null;
    let alloyNextUsageLine = null;
    let sawAlloyOrderingOpen = false;
    let sawAlloyNextDefinition = false;
    let alloyBooleanMisuseLine = null;
    let sawAlloyBooleanOpen = false;
    let sawAlloyBoolType = false;
    const fenceBodyLines = [];
    for (; fenceEndLine < lines.length; fenceEndLine++) {
      if (lines[fenceEndLine].trim() === '```') {
        foundEnd = true;
        break;
      }

      const line = lines[fenceEndLine];
      fenceBodyLines.push(line);

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
        const isCommentLine = trimmed.startsWith('//') || trimmed.startsWith('--');
        if (!isCommentLine) {
          if (!sawAlloyOrderingOpen && ALLOY_ORDERING_OPEN_PATTERN.test(line)) {
            sawAlloyOrderingOpen = true;
          }
          if (!sawAlloyNextDefinition && ALLOY_NEXT_DEFINITION_PATTERN.test(line)) {
            sawAlloyNextDefinition = true;
          }
          if (!sawAlloyBooleanOpen && ALLOY_BOOLEAN_OPEN_PATTERN.test(line)) {
            sawAlloyBooleanOpen = true;
          }
          if (!sawAlloyBoolType && ALLOY_BOOL_TYPE_PATTERN.test(line)) {
            sawAlloyBoolType = true;
          }
          if (alloyEnglishInfixLine === null && ALLOY_ENGLISH_INFIX_PATTERN.test(line)) {
            alloyEnglishInfixLine = fenceEndLine;
          }
          if (alloyNextUsageLine === null && ALLOY_NEXT_USAGE_PATTERN.test(line)) {
            alloyNextUsageLine = fenceEndLine;
          }
          if (
            alloyBooleanMisuseLine === null &&
            (ALLOY_BOOLEAN_TYPE_PATTERN.test(line) || ALLOY_BOOLEAN_LITERAL_PATTERN.test(line))
          ) {
            alloyBooleanMisuseLine = fenceEndLine;
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

    if (
      isStrictToolLabel &&
      fenceLang === 'alloy' &&
      alloyBooleanMisuseLine !== null &&
      !sawAlloyBooleanOpen &&
      !sawAlloyBoolType
    ) {
      errors.push({
        line: alloyBooleanMisuseLine + 1,
        message:
          `${standaloneCodeLabel} のAlloyコードブロック内で Boolean / True / False を使用していますが、` +
          '`open util/boolean` や `Bool` の利用が見つかりません。' +
          'boolean モジュールを明示するか、`set Time` などの Alloy らしい表現へ変更してください',
      });
    }

    if (!foundEnd) {
      errors.push({
        line: fenceStartLine + 1,
        message: `${standaloneCodeLabel} のコードブロックが閉じられていません（終了フェンス \`\`\` がありません）`,
      });
      continue;
    }

    if (isStrictToolLabel && registrationId !== null) {
      const commandLines = fenceBodyLines.map((line) => line.trim()).filter(Boolean);
      const expectedCommand = runnerCommand(registrationId);
      if (commandLines.length !== 1 || commandLines[0] !== expectedCommand) {
        errors.push({
          line: fenceStartLine + 2,
          message:
            `example contract ${registrationId} の bash command は次の1行と完全一致する必要があります: ` +
            expectedCommand,
        });
      }
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

function runSelfTest() {
  const parent = path.join(process.cwd(), 'tools', '.tmp');
  fs.mkdirSync(parent, { recursive: true });
  const root = fs.mkdtempSync(path.join(parent, 'tool-block-self-test-'));
  const manifestIds = new Set(['alloy-valid']);
  const fixtures = [
    {
      name: 'valid strict registration',
      expected: null,
      content: [
        '<!-- example-contract: alloy-valid -->',
        '【Tool-compliant (runs as-is)】',
        '```bash',
        'node scripts/run-example-manifest.js --id alloy-valid',
        '```',
      ].join('\n'),
    },
    {
      name: 'missing registration',
      expected: '直前に <!-- example-contract: ID --> がありません',
      content: [
        '【Tool-compliant (runs as-is)】',
        '```bash',
        'node scripts/run-example-manifest.js --id alloy-valid',
        '```',
      ].join('\n'),
    },
    {
      name: 'unknown registration',
      expected: 'manifest に存在しません',
      content: [
        '<!-- example-contract: missing-id -->',
        '【Tool-compliant (runs as-is)】',
        '```bash',
        'node scripts/run-example-manifest.js --id missing-id',
        '```',
      ].join('\n'),
    },
    {
      name: 'wrong runner command',
      expected: 'bash command は次の1行と完全一致',
      content: [
        '<!-- example-contract: alloy-valid -->',
        '【Tool-compliant (runs as-is)】',
        '```bash',
        'bash tools/alloy-check.sh examples/alloy/valid.als',
        '```',
      ].join('\n'),
    },
  ];

  try {
    for (let index = 0; index < fixtures.length; index += 1) {
      const fixture = fixtures[index];
      const filePath = path.join(root, `${index}.md`);
      fs.writeFileSync(filePath, `${fixture.content}\n`);
      const errors = checkFile(filePath, manifestIds);
      if (fixture.expected === null && errors.length !== 0) {
        throw new Error(`${fixture.name}: unexpected errors: ${errors.map((e) => e.message).join(' | ')}`);
      }
      if (fixture.expected && !errors.some((error) => error.message.includes(fixture.expected))) {
        throw new Error(`${fixture.name}: expected diagnostic not found: ${fixture.expected}`);
      }
      console.log(`PASS: ${fixture.name}`);
    }
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
  console.log('OK: tool block registration self-tests passed.');
}

function main() {
  if (process.argv.includes('--self-test')) {
    runSelfTest();
    return;
  }
  if (process.argv.length > 2) {
    console.error('Usage: node scripts/check-tool-blocks.js [--self-test]');
    process.exitCode = 2;
    return;
  }

  let manifest;
  try {
    ({ manifest } = loadManifest(process.cwd()));
  } catch (error) {
    reportError('examples/example-manifest.json', 1, error.message);
    process.exitCode = 1;
    return;
  }
  const manifestIds = new Set(
    Array.isArray(manifest.examples) ? manifest.examples.map((entry) => entry && entry.id).filter(Boolean) : [],
  );
  const files = getTrackedMarkdownFiles();
  const allErrors = [];

  for (const filePath of files) {
    const errors = checkFile(filePath, manifestIds);
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
