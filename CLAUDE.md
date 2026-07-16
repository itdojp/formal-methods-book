# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Japanese-language technical book project about "形式的手法の基礎と応用" (Foundations and Applications of Formal Methods). The book covers specification description, model checking, and theorem proving with an integrated understanding approach, teaching formal methods from theory to practice for reliable system development.

## Repository Structure

This project uses an in-repository bilingual builder and a pinned external **book-formatter** Book QA contract:

```text
formal-methods-book/
├── src/ja/                  # Canonical Japanese manuscript
├── src/en/                  # English translation manuscript
├── shared/                  # Locale-neutral shared assets
├── docs/                    # Generated Japanese Pages publish tree
│   └── en/                  # Generated English Pages publish tree
├── book-config.json         # Repository/edition manifest
├── book-config.ja.json      # Japanese edition metadata
├── book-config.en.json      # English edition metadata
├── publication-config.json  # Locale-neutral Jekyll/mobile policy
├── scripts/build.js         # Bilingual publish-tree builder
└── package.json             # QA/build commands
```

## Book Framework

**Current**: `scripts/build.js` maintains the bilingual publish tree. Book QA checks out `itdojp/book-formatter` at the immutable SHA documented in `README.md`; the formatter is not vendored into this repository.

## Key Commands and Workflows

### Development
```bash
npm ci                       # Restore the package-lock.json dependency graph
npm start                    # Build and serve docs/ on localhost:4321
npm run build:all            # Build both publish trees
npm run generate:metadata    # Regenerate Jekyll/navigation/mobile/TOC metadata
npm run check:metadata       # Validate canonical and generated metadata
npm run test:publication-build # Test source-to-publish rendering and cleanup safety
npm run deploy               # Publish docs/ with gh-pages (manual fallback)
```

### Content Management
```bash
npm run lint                # Check markdown formatting
npm run check-links         # Validate internal links
npm test                    # Run all tests (lint + links)
npm audit                   # Audit the root lockfile dependency graph
npm run examples:pr-quick   # Run the seven PR-lane formal examples
```

Do not commit `node_modules/`, `docs/_site/`, `.artifacts/`, or tool caches. Run `npm run check:repository-hygiene` before proposing repository-structure changes.

Edit reader-facing manuscript content only under `src/ja/**` or `src/en/**`. Do not edit generated Markdown under `docs/**` directly. Run `npm run build:all`, commit the resulting publication pages, and verify that a second build leaves `docs/**` unchanged.

## Content Guidelines

### Book Structure
- **4 Parts, 13 Chapters** covering formal methods comprehensively
- **Part I (基礎編)**: Foundations (Chapters 1-3) - Motivation and basic concepts
- **Part II (手法編)**: Methods (Chapters 4-7) - Major formal methods understanding
- **Part III (検証編)**: Verification (Chapters 8-10) - System correctness confirmation
- **Part IV (実践編)**: Practice (Chapters 11-13) - Real-world project application

### Technical Focus
- **Mathematical approach** to software design and verification
- Emphasis on **specification description** and **verification techniques**
- **Integrated understanding** of model checking and theorem proving
- **Practical application** to real software development projects

### Writing Style
- **Target Audience**: Computer science students, software engineers, researchers
- **Language**: Japanese (formal academic writing style - である調 with occasional です・ます調)
- **Approach**: Theory to practice with mathematical rigor
- **Level**: Intermediate to advanced (assumes programming experience)

### Technical Requirements
- **Format**: Markdown (CommonMark + extensions)
- **Encoding**: UTF-8
- **Line endings**: LF (Unix format)
- **Framework**: in-repository bilingual builder + Jekyll Pages + pinned external book-formatter QA

## Important Notes

1. **Content Focus**: Mathematical specification and verification methods
2. **GitHub Pages**: Deploys from `/docs` folder using Jekyll
3. **Author**: 太田和彦（株式会社アイティードゥ）
4. **Educational Goal**: Bridge theory and practice in formal methods
5. **Target**: CS students, software engineers working on critical systems

## Content Focus Areas

### Core Topics (13 Chapters)
1. **Why formal methods are necessary** - Software complexity and reliability challenges
2. **Bridge between mathematics and programming** - Mathematical thinking and programming
3. **Basic specification description** - Ambiguity in natural language vs mathematical precision
4. **Lightweight formal methods - Alloy** - Relational modeling and verification
5. **State-based specification - Z notation** - Mathematical notation for precise specification
6. **Process-centric description - CSP** - Concurrent systems and communication
7. **Time-handling specification - TLA+** - Temporal logic and distributed systems
8. **Model checking introduction** - Automated verification and state space exploration
9. **Theorem proving foundations** - Mechanized proof and proof assistants
10. **Program verification** - Hoare logic and correctness proofs
11. **Development process integration** - Practical adoption strategies
12. **Tools and automation** - Tool ecosystem and CI/CD integration
13. **Case studies** - Real-world applications and lessons learned

### Practical Applications
- Tool usage (Alloy Analyzer, TLC, Apalache, Lean, Rocq, Dafny, SPIN, NuSMV, CBMC)
- Case studies (Paris Metro Line 14, Amazon s2n, Microsoft TLA+)
- Integration with development processes
- Cost-benefit analysis and adoption strategies

## Quality Standards

- **Mathematical Rigor**: Precise mathematical notation and concepts
- **Practical Relevance**: Every concept includes practical application guidance
- **Progressive Learning**: Logical progression from foundations to advanced topics
- **Tool Integration**: Hands-on experience with formal methods tools

## Educational Approach

- **Issue-driven changes**: Treat the relevant GitHub Issue acceptance criteria as the change contract
- **Bilingual source policy**: Follow `BILINGUAL-WORKFLOW.md` and update `src/ja/**` before dependent translations/public output
- **SVG Diagrams**: Follow the repository's current layout/accessibility checks
- **Figure Numbering**: Format as 図N-M (N=chapter, M=sequential number in chapter)

## Contact Information

**Author**: 太田和彦（株式会社アイティードゥ）  
**Email**: knowledge@itdo.jp  
**GitHub**: [@itdojp](https://github.com/itdojp)  
**Organization**: 株式会社アイティードゥ
