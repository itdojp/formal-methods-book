#!/usr/bin/env node
'use strict';

const fs = require('fs');

const REQUIRED_REFERENCES = [
  {
    chapterPath: 'src/chapters/chapter04.md',
    examplePaths: [
      'examples/ch04/university-enrollment.als',
      'examples/alloy/trash-temporal.als',
    ],
  },
  {
    chapterPath: 'docs/chapters/chapter04/index.md',
    examplePaths: [
      'examples/ch04/university-enrollment.als',
      'examples/alloy/trash-temporal.als',
    ],
  },
  {
    chapterPath: 'src/chapters/chapter08.md',
    examplePaths: [
      'examples/ch08/spin/ltl-properties.pml',
      'examples/ch08/spin/producer-consumer.pml',
      'examples/ch08/nusmv/fairness.smv',
      'examples/ch08/nusmv/request-response.smv',
      'examples/ch08/cbmc/array-bounds.c',
    ],
  },
  {
    chapterPath: 'docs/chapters/chapter08/index.md',
    examplePaths: [
      'examples/ch08/spin/ltl-properties.pml',
      'examples/ch08/spin/producer-consumer.pml',
      'examples/ch08/nusmv/fairness.smv',
      'examples/ch08/nusmv/request-response.smv',
      'examples/ch08/cbmc/array-bounds.c',
    ],
  },
];

function reportError(filePath, lineNumber, message) {
  const safeMessage = String(message).replace(/\r?\n/g, ' ');
  console.error(`::error file=${filePath},line=${lineNumber}::${safeMessage}`);
}

function findLineNumber(content, needle) {
  const lines = content.split(/\r?\n/);
  for (let index = 0; index < lines.length; index++) {
    if (lines[index].includes(needle)) return index + 1;
  }
  return 1;
}

function main() {
  const errors = [];

  for (const entry of REQUIRED_REFERENCES) {
    const chapterContent = fs.readFileSync(entry.chapterPath, 'utf8');

    for (const examplePath of entry.examplePaths) {
      if (!fs.existsSync(examplePath)) {
        errors.push({
          filePath: entry.chapterPath,
          line: 1,
          message: `対応する example が存在しません: ${examplePath}`,
        });
      }

      if (!chapterContent.includes(examplePath)) {
        errors.push({
          filePath: entry.chapterPath,
          line: findLineNumber(chapterContent, 'examples/'),
          message: `本文から対応する example への導線がありません: ${examplePath}`,
        });
      }
    }
  }

  if (errors.length === 0) {
    console.log('OK: chapter/tool example links are present and all referenced example files exist.');
    return;
  }

  for (const error of errors) {
    reportError(error.filePath, error.line, error.message);
  }
  console.error(`Found ${errors.length} chapter/example mapping error(s).`);
  process.exitCode = 1;
}

main();
