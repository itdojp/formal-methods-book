#!/usr/bin/env node

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const repoRoot = path.resolve(__dirname, '..');

const forbiddenTrackedPrefixes = [
  'node_modules/',
  '_site/',
  'docs/_site/',
  'formal-methods-book/',
];

const obsoleteTemplatePaths = new Set([
  'COMPARISON.md',
  'DESIGN-PREVIEW.md',
  'DIAGRAM_ENHANCEMENT_REPORT.md',
  'EPUB-PDF-GUIDE.md',
  'FEEDBACK-COLLECTION.md',
  'HANDOVER-SUMMARY.md',
  'HANDOVER.md',
  'INTEGRATION_CHECKLIST.md',
  'MIGRATION-PLAN.md',
  'NEW-FEATURES.md',
  'QUALITY_REPORT.md',
  'book-config.sample.json',
  'book-formatter-config.json',
  'book-template-guide.md',
  'cspell.json',
  'design-preview.html',
  'it_book_proofreading_prompt.md',
  'jest.e2e.config.js',
  'mobile-config.json',
  'docs/assets/images/README-IMAGES.md',
  'docs/assets/images/book-publishing-template-ActionSecret.png',
  'docs/assets/images/book-publishing-template-ActionSecret2.png',
  'docs/assets/images/book-publishing-template-ActionSecretInput.png',
  'docs/assets/images/book-publishing-template-PAT.png',
  'docs/assets/images/book-publishing-template-repository-name.png',
  'docs/assets/images/book-publishing-template-use-this.png',
  'docs/assets/css/epub.css',
  'docs/assets/css/print.css',
  'docs/assets/css/search.css',
  'docs/assets/js/code-copy.js',
  'docs/assets/js/main.js',
  'docs/assets/js/mobile-navigation.js',
  'docs/assets/js/safe-main.js',
  'docs/assets/js/sidebar.js',
]);

function trackedPathProblems(trackedFiles) {
  const problems = [];
  for (const file of trackedFiles) {
    const prefix = forbiddenTrackedPrefixes.find((candidate) => file.startsWith(candidate));
    if (prefix) {
      problems.push(`generated or duplicate path is tracked: ${file}`);
    }
    if (obsoleteTemplatePaths.has(file)) {
      problems.push(`obsolete template path is tracked: ${file}`);
    }
  }
  return problems;
}

function extractFormatterPin(workflow) {
  const checkout = workflow.match(
    /repository:\s*itdojp\/book-formatter[\s\S]{0,400}?\n\s*ref:\s*([0-9a-f]{40})\s*(?:#.*)?$/m,
  );
  return checkout ? checkout[1] : null;
}

function unsupportedNpmScripts(text, availableScripts) {
  const problems = [];
  const references = text.matchAll(
    /\bnpm\s+(?:run\s+([A-Za-z0-9:_-]+)|(start|test|stop|restart))\b/g,
  );
  for (const match of references) {
    const script = match[1] || match[2];
    if (!availableScripts.has(script)) {
      problems.push(script);
    }
  }
  return [...new Set(problems)].sort();
}

function read(relativePath) {
  return fs.readFileSync(path.join(repoRoot, relativePath), 'utf8');
}

function runSelfTest() {
  const tracked = [
    'README.md',
    'node_modules/example/index.js',
    '_site/index.html',
    'docs/_site/index.html',
    'formal-methods-book/docs/assets/app.js',
    'MIGRATION-PLAN.md',
  ];
  const trackedProblems = trackedPathProblems(tracked);
  if (trackedProblems.length !== 5) {
    throw new Error(`tracked-path fixture: expected 5 problems, got ${trackedProblems.length}`);
  }

  const validWorkflow = `repository: itdojp/book-formatter\n          ref: ${'a'.repeat(40)}\n`;
  if (extractFormatterPin(validWorkflow) !== 'a'.repeat(40)) {
    throw new Error('formatter-pin fixture: immutable SHA was not extracted');
  }
  if (extractFormatterPin('repository: itdojp/book-formatter\n  ref: main\n') !== null) {
    throw new Error('formatter-pin fixture: mutable ref was accepted');
  }

  const unsupported = unsupportedNpmScripts(
    'npm run build, npm start, npm audit, npm run missing, npm run missing, and npm stop',
    new Set(['build', 'start']),
  );
  if (unsupported.length !== 2 || unsupported[0] !== 'missing' || unsupported[1] !== 'stop') {
    throw new Error('npm-script fixture: unsupported run/lifecycle commands were not detected');
  }

  console.log('OK: repository hygiene self-tests passed.');
}

function runCanonicalCheck() {
  const problems = [];
  const tracked = execFileSync('git', ['ls-files', '-z'], {
    cwd: repoRoot,
    encoding: 'utf8',
  }).split('\0').filter(Boolean);
  problems.push(...trackedPathProblems(tracked));

  const ignoreLines = new Set(
    read('.gitignore')
      .split(/\r?\n/)
      .map((line) => line.trim())
      .filter((line) => line && !line.startsWith('#')),
  );
  for (const required of [
    'node_modules/',
    '_site/',
    'docs/_site/',
    '.artifacts/',
    'tools/.cache/',
    'tools/.tmp/',
  ]) {
    if (!ignoreLines.has(required)) {
      problems.push(`.gitignore is missing required generated path: ${required}`);
    }
  }

  const packageJson = JSON.parse(read('package.json'));
  const packageLock = JSON.parse(read('package-lock.json'));
  if (packageLock.lockfileVersion !== 3) {
    problems.push(`package-lock.json must use lockfileVersion 3, got ${packageLock.lockfileVersion}`);
  }
  if (packageLock.name !== packageJson.name || packageLock.version !== packageJson.version) {
    problems.push('package.json and package-lock.json package identity/version differ');
  }

  const workflow = read('.github/workflows/book-qa.yml');
  const formatterPin = extractFormatterPin(workflow);
  if (!formatterPin) {
    problems.push('Book QA must pin itdojp/book-formatter to an immutable 40-character commit SHA');
  }

  const readme = read('README.md');
  if (!readme.includes('npm ci') || !readme.includes('package-lock.json')) {
    problems.push('README must document package-lock.json and npm ci as the dependency contract');
  }
  if (formatterPin && !readme.includes(formatterPin)) {
    problems.push(`README formatter pin does not match Book QA ref ${formatterPin}`);
  }

  const changelog = read('CHANGELOG.md');
  const staleClaims = [
    'All notable changes to this book-publishing-template',
    'PDF/EPUB support',
    'Incremental Builds',
    'Automatic filtering of private comments',
    'Zenn, and Kindle support',
    'Template Integration Checklist',
  ];
  for (const claim of staleClaims) {
    if (changelog.includes(claim)) {
      problems.push(`CHANGELOG retains an obsolete template claim: ${claim}`);
    }
  }

  const availableScripts = new Set(Object.keys(packageJson.scripts || {}));
  for (const document of ['README.md', 'CONTRIBUTING.md', 'BILINGUAL-WORKFLOW.md', 'CLAUDE.md']) {
    for (const command of unsupportedNpmScripts(read(document), availableScripts)) {
      problems.push(`${document} references undefined command: npm run ${command}`);
    }
  }

  if (problems.length > 0) {
    for (const problem of problems) {
      console.error(`ERROR: ${problem}`);
    }
    process.exit(1);
  }

  console.log(
    `OK: repository hygiene passed (${tracked.length} tracked files, formatter ${formatterPin.slice(0, 12)}).`,
  );
}

if (process.argv.includes('--self-test')) {
  runSelfTest();
} else {
  runCanonicalCheck();
}

module.exports = {
  extractFormatterPin,
  trackedPathProblems,
  unsupportedNpmScripts,
};
