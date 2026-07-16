#!/usr/bin/env node
'use strict';

const assert = require('assert');
const fs = require('fs');
const path = require('path');
const { loadPublicationModel } = require('./lib/publication-metadata');
const { renderEditionPages } = require('./lib/publication-build');
const {
  addGlossaryTermAnchors,
  baseKramdownId,
  parseMarkdownSections,
  renderSearchIndex,
  serializeSearchIndex,
  uniqueKramdownId,
} = require('./lib/search-index');
const browserSearch = require('../docs/assets/js/search.js');

const repoRoot = path.resolve(__dirname, '..');

assert.strictEqual(
  baseKramdownId('第7章：時間を扱う仕様記述 - TLA+ 入門'),
  '第7章時間を扱う仕様記述---tla-入門',
);
assert.strictEqual(baseKramdownId('Economic Evaluation'), 'economic-evaluation');
assert.strictEqual(baseKramdownId('Tool lane {#tool-lane-inventory}'), 'tool-lane-inventory');
assert.strictEqual(
  baseKramdownId('LTLの基本例（安全性・活性）{: #ltl-basic-examples }'),
  'ltlの基本例安全性活性-ltl-basic-examples-',
);

const usedIds = new Set();
assert.strictEqual(uniqueKramdownId('Challenges and Limits', usedIds), 'challenges-and-limits');
assert.strictEqual(uniqueKramdownId('Challenges and Limits', usedIds), 'challenges-and-limits-1');

const anchoredGlossary = addGlossaryTermAnchors([
  '# Glossary',
  '',
  '**Rocq**: A proof assistant.',
  '',
  '**Rocq**: A duplicate fixture.',
].join('\n'));
assert.match(anchoredGlossary, /id="glossary-rocq"/u);
assert.match(anchoredGlossary, /id="glossary-rocq-1"/u);

const fixtureSections = parseMarkdownSections([
  '---',
  'title: ignored',
  '---',
  '# Fixture',
  '<!-- hidden phrase -->',
  'Visible introduction.',
  '```text',
  'secret code duplicate',
  '```',
  '## Explicit heading {#fixed-heading}',
  'Searchable prose.',
  '<span id="glossary-rocq" class="search-term-anchor" aria-hidden="true"></span>**Rocq**: Canonical term.',
].join('\n'), { title: 'Fixture' });
assert.strictEqual(fixtureSections.length, 3);
assert.strictEqual(fixtureSections[1].anchor, 'fixed-heading');
assert.strictEqual(fixtureSections[2].kind, 'term');
assert.strictEqual(fixtureSections[2].anchor, 'glossary-rocq');
assert.ok(!fixtureSections.some((entry) => entry.textLines.join(' ').includes('hidden phrase')));
assert.ok(!fixtureSections.some((entry) => entry.textLines.join(' ').includes('secret code duplicate')));

const model = loadPublicationModel(repoRoot);
for (const locale of Object.keys(model.manifest.editions)) {
  const pages = renderEditionPages(repoRoot, model, locale);
  const first = renderSearchIndex({ repoRoot, model, locale, pages });
  const second = renderSearchIndex({ repoRoot, model, locale, pages });
  assert.strictEqual(serializeSearchIndex(first), serializeSearchIndex(second), `${locale} index is not deterministic`);
  assert.strictEqual(first.entryCount, first.entries.length);
  assert.ok(first.entries.length > 500, `${locale} index unexpectedly small`);
}

const sampleEntries = [
  {
    locale: 'ja', section: 'special', title: 'LeanDojo', chapter: '用語集', heading: 'LeanDojo',
    text: 'LeanDojo の定義', aliases: [], url: '/formal-methods-book/glossary/#glossary-leandojo',
  },
  {
    locale: 'ja', section: 'chapters', title: '学習ベースの証明探索', chapter: '第9章', heading: '学習ベースの証明探索',
    text: 'LeanDojo は Lean リポジトリから証明状態を抽出する。', aliases: [],
    url: '/formal-methods-book/chapters/chapter09/#学習ベースの証明探索',
  },
];
const leanResults = browserSearch.searchEntries(sampleEntries, 'LeanDojo', 'ja');
assert.strictEqual(leanResults[0].section, 'chapters', 'chapter content must be preferred over the glossary shortcut');
assert.deepStrictEqual(browserSearch.keyboardAction('ArrowDown', -1, 3), { type: 'select', index: 0 });
assert.deepStrictEqual(browserSearch.keyboardAction('ArrowUp', 0, 3), { type: 'select', index: 2 });
assert.deepStrictEqual(browserSearch.keyboardAction('Enter', 1, 3), { type: 'activate', index: 1 });
assert.deepStrictEqual(browserSearch.keyboardAction('Escape', 1, 3), { type: 'close', index: -1 });
assert.deepStrictEqual(
  browserSearch.highlightSegments('<img src=x onerror=alert(1)>', '<img'),
  [
    { text: '<img', match: true },
    { text: ' src=x onerror=alert(1)>', match: false },
  ],
  'highlighting must return text segments rather than executable markup',
);
assert.throws(() => browserSearch.validateIndexPayload({ schemaVersion: 1, locale: 'en', entryCount: 0, entries: [] }, 'ja'));
assert.throws(() => browserSearch.validateIndexPayload({
  schemaVersion: 1,
  project: 'formal-methods-book',
  locale: 'ja',
  entryCount: 1,
  entries: [{
    id: 'bad', locale: 'ja', title: 'bad', chapter: 'bad', heading: 'bad', text: 'bad', aliases: [], url: 'javascript:alert(1)',
  }],
}, 'ja'));
assert.strictEqual(
  browserSearch.searchEntries(sampleEntries, `${'x'.repeat(128)}LeanDojo`, 'ja').length,
  0,
  'queries are bounded before matching',
);

class FakeClassList {
  constructor() { this.values = new Set(); }
  toggle(name, enabled) {
    if (enabled) this.values.add(name);
    else this.values.delete(name);
  }
}

class FakeElement {
  constructor(tagName, id = '') {
    this.tagName = tagName;
    this.id = id;
    this.dataset = {};
    this.attributes = new Map();
    this.children = [];
    this.listeners = new Map();
    this.classList = new FakeClassList();
    this.hidden = false;
    this.textContent = '';
    this.value = '';
    this.clicked = false;
  }
  setAttribute(name, value) { this.attributes.set(name, String(value)); }
  removeAttribute(name) { this.attributes.delete(name); }
  getAttribute(name) { return this.attributes.get(name); }
  appendChild(child) { this.children.push(child); return child; }
  append(...children) { this.children.push(...children); }
  replaceChildren(...children) { this.children = [...children]; }
  addEventListener(type, listener) { this.listeners.set(type, listener); }
  dispatch(type, event) { return this.listeners.get(type)?.(event); }
  querySelectorAll(selector) {
    if (selector !== '[role="option"]') return [];
    return this.children.filter((child) => child?.getAttribute?.('role') === 'option');
  }
  scrollIntoView() {}
  click() { this.clicked = true; }
}

class FakeDocument {
  constructor(elements) {
    this.elements = elements;
    this.listeners = new Map();
  }
  getElementById(id) { return this.elements[id] || null; }
  createElement(tagName) { return new FakeElement(tagName); }
  createTextNode(text) { return { nodeType: 3, textContent: text }; }
  addEventListener(type, listener) { this.listeners.set(type, listener); }
}

async function testDomController() {
  const input = new FakeElement('input', 'search-input');
  input.dataset = {
    locale: 'ja',
    indexUrl: '/formal-methods-book/assets/search-index.ja.json',
    loadingLabel: '読み込み中',
    noResultsLabel: '結果なし',
    loadErrorLabel: '失敗',
    resultCountLabel: '{count}件',
  };
  const results = new FakeElement('div', 'search-results');
  const status = new FakeElement('div', 'search-status');
  const fakeDocument = new FakeDocument({
    'search-input': input,
    'search-results': results,
    'search-status': status,
  });
  const payload = {
    schemaVersion: 1,
    project: 'formal-methods-book',
    locale: 'ja',
    entryCount: 1,
    entries: [{
      id: 'safe', locale: 'ja', pageId: 'chapter09', section: 'chapters', title: '<b>LeanDojo</b>',
      chapter: '第9章', heading: 'LeanDojo', text: '<img onerror=alert(1)> LeanDojo', aliases: [],
      url: '/formal-methods-book/chapters/chapter09/#leandojo',
    }],
  };
  const controller = browserSearch.createController(
    fakeDocument,
    { setTimeout: (callback) => { callback(); return 1; }, clearTimeout: () => {} },
    async () => ({ ok: true, json: async () => payload }),
  );
  await controller.ensureIndex();
  controller.render('LeanDojo');
  assert.strictEqual(input.getAttribute('aria-expanded'), 'true');
  assert.strictEqual(results.children.length, 1);
  assert.strictEqual(results.children[0].tagName, 'a');
  assert.strictEqual(results.children[0].getAttribute('role'), 'option');
  assert.strictEqual(results.children[0].children[1].children[0].nodeType, 3, 'malicious title remains a text node');
  let prevented = false;
  input.dispatch('keydown', { key: 'ArrowDown', preventDefault: () => { prevented = true; } });
  assert.ok(prevented);
  assert.strictEqual(input.getAttribute('aria-activedescendant'), 'search-option-0');
  input.dispatch('keydown', { key: 'Enter', preventDefault: () => {} });
  assert.ok(results.children[0].clicked, 'Enter activates the selected result');
  input.dispatch('keydown', { key: 'Escape', preventDefault: () => {} });
  assert.strictEqual(input.getAttribute('aria-expanded'), 'false');
}

const searchSource = fs.readFileSync(path.join(repoRoot, 'docs/assets/js/search.js'), 'utf8');
assert.ok(!/\.innerHTML\s*=/u.test(searchSource), 'search UI must not render index content through innerHTML');
assert.ok(!/insertAdjacentHTML/u.test(searchSource), 'search UI must not inject HTML strings');

testDomController().then(() => {
  console.log('Search index and browser search tests passed.');
}).catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
