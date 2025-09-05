#!/usr/bin/env node
/*
  Simple builder: copies src markdown into docs structure that matches docs/index.md links.
  - src/appendices/appendix-[id].md -> docs/appendices/appendix-[id]/index.md
  Note: chapters are maintained under docs/ with Jekyll frontmatter; this builder does NOT touch chapters.
*/
const fs = require('fs');
const path = require('path');

const repoRoot = path.resolve(__dirname, '..');
const src = path.join(repoRoot, 'src');
const docs = path.join(repoRoot, 'docs');

function ensureDir(p) {
  fs.mkdirSync(p, { recursive: true });
}

function copyToDirAsIndex(srcFile, dstDir) {
  const content = fs.readFileSync(srcFile, 'utf8');
  ensureDir(dstDir);
  const dstFile = path.join(dstDir, 'index.md');
  fs.writeFileSync(dstFile, content);
}

function cleanSubdir(dir) {
  if (!fs.existsSync(dir)) return;
  for (const entry of fs.readdirSync(dir)) {
    const p = path.join(dir, entry);
    fs.rmSync(p, { recursive: true, force: true });
  }
}

// No chapter build here: docs/chapters includes Jekyll frontmatter and layout.

function buildAppendices() {
  const appSrc = path.join(src, 'appendices');
  const appDst = path.join(docs, 'appendices');
  ensureDir(appDst);
  cleanSubdir(appDst);
  if (!fs.existsSync(appSrc)) return;
  const files = fs.readdirSync(appSrc);
  for (const f of files) {
    if (!f.endsWith('.md')) continue;
    const id = path.basename(f, '.md');
    copyToDirAsIndex(path.join(appSrc, f), path.join(appDst, id));
  }
}

function main() {
  ensureDir(docs);
  buildAppendices();
  console.log('Built docs structure from src/.');
}

main();
