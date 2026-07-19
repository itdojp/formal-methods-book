#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const { loadPublicationModel } = require('./lib/publication-metadata');
const { insertTranslationNotice, loadTranslationManifest } = require('./lib/translation-status');

const repoRoot = path.resolve(__dirname, '..');
const errors = [];

function read(filePath) {
  return fs.readFileSync(path.join(repoRoot, filePath), 'utf8').replace(/\r\n/g, '\n');
}

function lineOf(content, needle) {
  const index = content.indexOf(needle);
  return index < 0 ? 1 : content.slice(0, index).split('\n').length;
}

function auditContent(content, required, forbidden) {
  const findings = [];
  for (const marker of required) {
    if (!content.includes(marker)) findings.push({ kind: 'missing', marker });
  }
  for (const marker of forbidden) {
    if (content.includes(marker)) findings.push({ kind: 'forbidden', marker });
  }
  return findings;
}

function auditFile(filePath, required, forbidden = []) {
  const content = read(filePath);
  for (const finding of auditContent(content, required, forbidden)) {
    const message = finding.kind === 'missing'
      ? `required assurance-boundary marker is missing: ${finding.marker}`
      : `obsolete or unconditional assurance claim remains: ${finding.marker}`;
    errors.push({ filePath, line: lineOf(content, finding.marker), message });
  }
}

function stripFrontMatter(content) {
  if (!content.startsWith('---\n')) return content;
  const end = content.indexOf('\n---\n', 4);
  return end < 0 ? content : content.slice(end + 5);
}

let translationManifest;

function addEnglishTranslationStatus(content, sourcePath) {
  if (!translationManifest) {
    const publicationModel = loadPublicationModel(repoRoot);
    translationManifest = loadTranslationManifest(repoRoot, publicationModel);
  }
  const relativePath = sourcePath.replace(/^src\/en\//, '');
  const entry = translationManifest.pages[relativePath];
  if (!entry) throw new Error(`translation status is missing for ${sourcePath}`);
  return insertTranslationNotice(content, entry);
}

function normalizeGeneratedBody(content) {
  return content
    .replace(/^<span id="glossary-[^"]+" class="search-term-anchor" aria-hidden="true"><\/span>/gm, '')
    .replace(/\[(examples\/[A-Za-z0-9_./-]+)\]\([^)]+\)/g, '[$1](example-link:$1)')
    .trimEnd();
}

function requireGeneratedMatch(sourcePath, publicPath, locale) {
  let source = read(sourcePath);
  if (locale === 'en') source = addEnglishTranslationStatus(source, sourcePath);
  const published = stripFrontMatter(read(publicPath));
  if (normalizeGeneratedBody(source) !== normalizeGeneratedBody(published)) {
    errors.push({
      filePath: publicPath,
      line: 1,
      message: `${publicPath} is stale; run npm run build:all after updating ${sourcePath}`,
    });
  }
}

function requireSharedSectionMatch(sourcePath, publicPath, startMarker, endMarker) {
  const source = read(sourcePath);
  const published = read(publicPath);
  const start = source.indexOf(startMarker);
  const end = source.indexOf(endMarker, start + startMarker.length);
  if (start < 0 || end < 0) {
    errors.push({
      filePath: sourcePath,
      line: lineOf(source, startMarker),
      message: `cannot extract guarded section from ${startMarker} to ${endMarker}`,
    });
    return;
  }
  const section = source.slice(start, end + endMarker.length);
  if (!published.includes(section)) {
    errors.push({
      filePath: publicPath,
      line: lineOf(published, startMarker),
      message: `hand-maintained public section differs from ${sourcePath}: ${startMarker}`,
    });
  }
}

function runSelfTest() {
  assert.deepStrictEqual(auditContent('alpha beta', ['alpha'], ['gamma']), []);
  assert.deepStrictEqual(auditContent('alpha beta', ['gamma'], ['beta']), [
    { kind: 'missing', marker: 'gamma' },
    { kind: 'forbidden', marker: 'beta' },
  ]);
  assert.deepStrictEqual(
    auditContent('finite model with TypeOK', ['finite model', 'TypeOK'], ['static type system']),
    [],
  );
  assert.deepStrictEqual(
    auditContent(
      'simulationによるランダム欠陥探索 反例が見つからなかったという事実は、性質の証明ではありません。 -simulate file=/absolute/path/trace,num=1000',
      ['simulationによるランダム欠陥探索', '性質の証明ではありません', '-simulate file=/absolute/path/trace,num=1000'],
      ['確率的検証'],
    ),
    [],
  );
  assert.deepStrictEqual(
    auditContent('### 確率的検証', [], ['### 確率的検証']),
    [{ kind: 'forbidden', marker: '### 確率的検証' }],
  );
  assert.strictEqual(stripFrontMatter('---\ntitle: T\n---\nBody\n'), 'Body\n');
  assert.strictEqual(
    normalizeGeneratedBody('[examples/a.smv](../../../examples/a.smv)'),
    normalizeGeneratedBody('[examples/a.smv](https://example.invalid/revision/examples/a.smv)'),
  );
  assert.strictEqual(
    normalizeGeneratedBody('<span id="glossary-model-checking" class="search-term-anchor" aria-hidden="true"></span>**Model checking**'),
    normalizeGeneratedBody('**Model checking**'),
  );
  console.log('OK: assurance-boundary checker self-tests passed.');
}

if (process.argv.includes('--self-test')) {
  runSelfTest();
  process.exit(0);
}

const jaChapter7Required = [
  '線形化可能（linearizable）な一貫性',
  '非故障ノードが受け取ったすべての要求',
  '完全非同期モデル',
  '故障検出器（failure detector）',
  '不可能性定理は結論だけでなく',
  '実装コード、モデルに含めなかった故障',
  '### simulationによるランダム欠陥探索',
  'simulation は、網羅的な model checking でも確率モデル検査でもありません',
  'simulationで反例が見つからなかったという事実は、性質の証明ではありません',
  '-simulate file=/absolute/path/simulation-trace,num=1000',
  'TLA+ tools v1.7.4',
  'https://github.com/tlaplus/tlaplus/blob/v1.7.4/tlatools/org.lamport.tlatools/src/tlc2/TLC.java#L1451-L1466',
];
const jaChapter7Forbidden = [
  'すべてのノードが同じデータを見る',
  '非同期分散システムにおいて、一つでもノード故障がある場合、決定論的な合意アルゴリズムは存在しない',
  '理論的な正しさと実用的な堅牢性を同時に保証',
  '### 確率的検証',
  'ランダムサンプリングによる確率的検証',
];
const enChapter7Required = [
  'atomic, or linearizable, behavior',
  'every request received by a non-failing node',
  'completely asynchronous model',
  'failure detectors expose structured suspicions',
  'a package of computational, failure, communication, and guarantee assumptions',
  'does not establish correctness of the implementation',
  '### Randomized Defect Search with Simulation',
  'Simulation is neither exhaustive model checking nor probabilistic model',
  'Finding no counterexample in simulation does not prove the property',
  '-simulate file=/absolute/path/simulation-trace,num=1000',
  'TLA+ tools v1.7.4',
  'https://github.com/tlaplus/tlaplus/blob/v1.7.4/tlatools/org.lamport.tlatools/src/tlc2/TLC.java#L1451-L1466',
];
const enChapter7Forbidden = [
  'all nodes observe the same data',
  'if even a single node can fail, there is no deterministic consensus algorithm',
  'check the essential correctness of the algorithm',
  '### Probabilistic or Sampling-Based Checking',
  'bounded or sampling-oriented approaches may be used operationally',
];

for (const filePath of ['src/ja/chapters/chapter07.md', 'docs/chapters/chapter07/index.md']) {
  auditFile(filePath, jaChapter7Required, jaChapter7Forbidden);
}
for (const filePath of ['src/en/chapters/chapter07.md', 'docs/en/chapters/chapter07/index.md']) {
  auditFile(filePath, enChapter7Required, enChapter7Forbidden);
}

const jaChapter8Required = [
  '指定した有限状態モデル',
  '`TypeOK` や `TypeInvariant`',
  '保証の上下関係ではありません',
  'bitstate hashing は近似',
  'timeout や `unknown` は成立確認ではない',
  '境界外は未検査',
];
const jaChapter8Forbidden = [
  '**型システム**: 豊富なデータ型のサポート',
  '**完全検証** → シンボリック手法',
  '**バグ発見** → 明示的検証',
  'コンピュータが「確実に正しい」',
];
const enChapter8Required = [
  'specified finite-state model',
  '`TypeOK` or `TypeInvariant`',
  'not a hierarchy of assurance',
  'Bitstate hashing is approximate',
  'Timeout or `unknown` is not confirmation',
  'Executions beyond the bound are unchecked',
];
const enChapter8Forbidden = [
  'systematically explores *all possible execution paths*',
  '**full verification where possible** -> symbolic methods',
  '**bug finding** -> explicit-state methods',
];

for (const filePath of ['src/ja/chapters/chapter08.md', 'docs/chapters/chapter08/index.md']) {
  auditFile(filePath, jaChapter8Required, jaChapter8Forbidden);
}
for (const filePath of ['src/en/chapters/chapter08.md', 'docs/en/chapters/chapter08/index.md']) {
  auditFile(filePath, enChapter8Required, enChapter8Forbidden);
}

const jaChapter9Required = [
  '`Γ ⊢ φ`',
  '`Γ ⊨ φ`',
  '古典一階述語論理',
  '高階論理、依存型理論',
  'Rocq の `Admitted`、Lean の `sorry` / `admit`',
  '外部ソルバ・プラグイン',
  '抽出・コード生成・native evaluation',
  '検証済み証明ではない',
  'クリティカル部分の証明義務を完了',
];
const jaChapter9Forbidden = [
  '「有限の範囲での完全性」を提供',
  '推論規則により証明できるものは、すべて真である',
  '信頼核は数千行程度',
  'Admitted. (* 詳細は省略 *)',
  '論理的な正しさを保証します',
  'クリティカル部分の完全検証',
];
const enChapter9Required = [
  '`Γ ⊢ φ`',
  '`Γ ⊨ φ`',
  'classical first-order logic',
  'higher-order logic, dependent type theory',
  'Rocq `Admitted`, Lean `sorry` / `admit`',
  'External solver or plugin',
  'Extraction, code generation, or native evaluation',
  'not a checked completed proof',
  "close the critical core's stated proof obligations",
];
const enChapter9Forbidden = [
  'then it is enough to trust that kernel',
  'only a few thousand lines of OCaml',
  'everything provable in the system is true',
  'The detailed reflective proof is omitted',
  'fully verify the critical core',
];

for (const filePath of ['src/ja/chapters/chapter09.md', 'docs/chapters/chapter09/index.md']) {
  auditFile(filePath, jaChapter9Required, jaChapter9Forbidden);
}
for (const filePath of ['src/en/chapters/chapter09.md', 'docs/en/chapters/chapter09/index.md']) {
  auditFile(filePath, enChapter9Required, enChapter9Forbidden);
}

auditFile('src/ja/glossary/index.md', [
  '**CAP 定理**',
  '**FLP 不可能性定理**',
  '**健全性（Soundness）**',
  '**完全性（Completeness）**',
  '**trusted kernel（信頼核）**',
  '`TypeOK` / `TypeInvariant`',
]);
auditFile('src/en/glossary/index.md', [
  '**CAP theorem**',
  '**FLP impossibility result**',
  '**Soundness**',
  '**Completeness**',
  '**Trusted kernel**',
  '`TypeOK` or `TypeInvariant`',
]);
auditFile('glossary-terms.md', [
  '**CAP 定理**',
  '**FLP 不可能性定理**',
  '**健全性（Soundness）**',
  '**完全性（Completeness）**',
  '**trusted kernel（信頼核）**',
  '`TypeOK` / `TypeInvariant`',
]);

const primarySourceUrls = [
  'https://lamport.azurewebsites.net/pubs/spec-book-chap.pdf',
  'https://github.com/nimble-code/Spin/blob/4883fbb1b1ef1f75fa9dda78efe1ad8910baf819/Man/spin.1',
  'https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf',
  'https://diffblue.github.io/cbmc/background-concepts.html',
  'https://rocq-prover.org/doc/v9.0/refman/proofs/writing-proofs/proof-mode.html',
  'https://lean-lang.org/doc/reference/latest/Axioms/',
  'https://www.cs.princeton.edu/courses/archive/spr22/cos418/papers/cap.pdf',
  'https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf',
];
auditFile('src/ja/appendices/appendix-e.md', primarySourceUrls);
auditFile('src/en/appendices/appendix-e.md', primarySourceUrls);

// Selected sections receive an additional semantic guard. Global
// source/publication equality is checked by the publication builder contract.
for (const [sourcePath, publicPath, startMarker, endMarker] of [
  ['src/ja/chapters/chapter07.md', 'docs/chapters/chapter07/index.md', '### 一貫性と可用性のトレードオフ', '### 非決定性の管理'],
  ['src/ja/chapters/chapter07.md', 'docs/chapters/chapter07/index.md', '### 合意の困難性', '### 状態の爆発'],
  ['src/ja/chapters/chapter08.md', 'docs/chapters/chapter08/index.md', '### TLC：TLA+ の実行エンジン', '**TLA+ 仕様例**'],
  ['src/ja/chapters/chapter08.md', 'docs/chapters/chapter08/index.md', '### 方式、検査範囲、完走結果の比較', '### ツール選択の決定要因'],
  ['src/ja/chapters/chapter09.md', 'docs/chapters/chapter09/index.md', '### 信頼性の確立', '### 証明の再利用と蓄積'],
  ['src/ja/chapters/chapter09.md', 'docs/chapters/chapter09/index.md', '### 演繹系と意味論に対する健全性と完全性', '### 直観主義論理と古典論理'],
]) {
  requireSharedSectionMatch(sourcePath, publicPath, startMarker, endMarker);
}

// Selected pages additionally bind the assurance markers to their generated
// publication bodies.
for (const [sourcePath, publicPath, locale] of [
  ['src/en/chapters/chapter07.md', 'docs/en/chapters/chapter07/index.md', 'en'],
  ['src/en/chapters/chapter08.md', 'docs/en/chapters/chapter08/index.md', 'en'],
  ['src/en/chapters/chapter09.md', 'docs/en/chapters/chapter09/index.md', 'en'],
  ['src/ja/appendices/appendix-e.md', 'docs/appendices/appendix-e/index.md', 'ja'],
  ['src/en/appendices/appendix-e.md', 'docs/en/appendices/appendix-e/index.md', 'en'],
  ['src/ja/glossary/index.md', 'docs/glossary/index.md', 'ja'],
  ['src/en/glossary/index.md', 'docs/en/glossary/index.md', 'en'],
]) {
  requireGeneratedMatch(sourcePath, publicPath, locale);
}

if (errors.length > 0) {
  for (const error of errors) {
    const message = String(error.message).replace(/\r?\n/g, ' ');
    console.error(`::error file=${error.filePath},line=${error.line}::${message}`);
  }
  console.error(`Found ${errors.length} assurance-boundary contract error(s).`);
  process.exitCode = 1;
} else {
  console.log('OK: model-checking, logic, proof-assistant, CAP, and FLP assurance boundaries match.');
}
