#!/usr/bin/env node
/*
  Simple builder: copies src markdown into docs structure that matches docs/index.md links.
  - src/chapters/chapterXX.md -> docs/chapters/chapterXX/index.md
  - src/appendices/appendix-[id].md -> docs/appendices/appendix-[id]/index.md
  Leaves docs/index.md as-is.
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

function buildChapters() {
  const chaptersSrc = path.join(src, 'chapters');
  const chaptersDst = path.join(docs, 'chapters');
  ensureDir(chaptersDst);
  cleanSubdir(chaptersDst);
  const files = fs.existsSync(chaptersSrc) ? fs.readdirSync(chaptersSrc) : [];
  for (const f of files) {
    if (!f.endsWith('.md')) continue;
    const id = path.basename(f, '.md');
    copyToDirAsIndex(path.join(chaptersSrc, f), path.join(chaptersDst, id));
  }
}

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
  buildChapters();
  buildAppendices();
  console.log('Built docs structure from src/.');
}

main();
