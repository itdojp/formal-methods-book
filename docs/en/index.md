---
layout: book
title: "Formal Methods: Foundations and Applications"
description: "A practical introduction to mathematically rigorous software design, from specification and model checking to theorem proving and program verification."
locale: "en"
lang: "en"
source_path: "src/en/index.md"
---
# Formal Methods: Foundations and Applications

Formal methods are often presented in one of two unhelpful ways: as abstract
mathematics with little engineering payoff, or as tool manuals that explain
commands without explaining why the method matters. This book takes a third
path.

It treats specification, model checking, theorem proving, and program
verification as one engineering discipline for building dependable software.
The goal is not to turn every reader into a verification specialist. The goal
is to help readers decide where formal methods pay off, how to adopt them
incrementally, and how to read verification results critically.

## Questions This Book Helps You Answer

- Which parts of a system should be specified precisely, and which parts can
  remain informal without creating unnecessary risk?
- When is model checking enough, and when is theorem proving or program
  verification worth the extra cost?
- How should you read a counterexample, proof obligation, or verification
  result without treating the tool as a black box?
- How do you introduce formal methods incrementally, without turning adoption
  into an all-or-nothing process?

These questions are answered through comparative chapters, small but concrete
examples, and later chapters on adoption, tooling, and case studies.

## Connecting Formal Methods to Test Strategy

Formal methods do not replace testing. They make requirements, invariants,
counterexamples, and proof obligations explicit so that testing and review can
focus on the right risks. For each pull request or design review, record the
following responsibility split.

| Activity | Primary responsibility | Connection to formal methods | Evidence to keep in the PR |
| --- | --- | --- | --- |
| Tests / evals / benchmarks | Check observable implementation behavior for selected inputs and scenarios | Derive boundary cases, equivalence classes, and regression cases from specifications and counterexamples | Commands, data set, expected result, and failure logs |
| Static analysis / types / contracts | Detect syntax, type, data-flow, and local contract violations early | Map preconditions, postconditions, and invariants onto code boundaries | Target, rule set, and any justified exception |
| Model checking | Explore safety, liveness, and deadlock properties within an explicit state space | Use Alloy, TLA+, CSP, or a similar model to inspect an abstraction | Scope, depth, seed, checked property, and counterexample trace |
| Theorem proving / program verification | Prove stronger correctness claims under stated assumptions | Manage proof obligations with Hoare logic, Dafny, Rocq, Lean, or related tools | Theorem statement, assumptions, target, and any unproved part |
| Human review | Judge assumptions, abstractions, uncovered behavior, and operational risk | Review requirement validity and cost-benefit beyond what verifiers can decide | Change decision, residual risk, and rationale for methods not used |

Use this table together with
[Appendix F: Practical Playbook for AI-Assisted Formal Methods]({{ '/en/appendices/appendix-f/' | relative_url }}).
When AI drafts specifications or invariants, keep final judgment separated
between verifiers, CI, and human review.

## Intended Audience

This book is written for the following readers:

- **Software engineers and architects** who want a more rigorous way to reason
  about behavior, constraints, and system assumptions
- **Quality, test, and reliability engineers** who need more than testing
  alone can provide
- **Engineers working on safety-, security-, or correctness-critical systems**
- **Students and researchers** who want a bridge between foundational ideas and
  engineering practice

## Who Should Not Use This Book as Their First Stop

This book is less suitable if you need any of the following:

- a certification handbook focused on one regulatory standard
- a language reference manual for a single tool
- an introduction to programming or discrete mathematics from first principles

## Prerequisites

To get the most out of this book, you should already be comfortable with the
following basics:

- **Programming**: basic coding experience, standard data structures, and the
  fundamentals of procedural or object-oriented development
- **Mathematics**: sets, logic, functions, and basic discrete reasoning
- **Software engineering**: requirements, design, testing, and change
  management

The book uses mathematical notation throughout, but it introduces the required
concepts carefully. Advanced mathematics is not required.

## Choose a Starting Path

- **New to formal methods**: start with
  [Introduction]({{ '/en/introduction/' | relative_url }}), then read Chapters
  1-3 and continue through Chapters 4-8 so that you understand why precise
  specifications and verification properties matter before going deeper into
  tools
- **Architecture and design decisions**: read Chapters 1-4, Chapter 7, Chapter
  11, and Chapter 13 to compare modeling styles and see where formalization
  changes design trade-offs
- **Verification and proof work**: read Chapters 1-3, then use Chapters 8-10
  as the backbone of the book, with
  [Appendix B]({{ '/en/appendices/appendix-b/' | relative_url }}) and
  [Appendix E]({{ '/en/appendices/appendix-e/' | relative_url }}) nearby for
  tool setup and primary sources
- **Adoption and rollout**: read Chapters 1, 3, and 11-13 together with
  [Appendix D]({{ '/en/appendices/appendix-d/' | relative_url }}),
  [Appendix E]({{ '/en/appendices/appendix-e/' | relative_url }}), and
  [Appendix F]({{ '/en/appendices/appendix-f/' | relative_url }}) to define a
  pilot scope, review packet, and evidence trail
- **Returning as a reference reader**: start from the
  [Glossary]({{ '/en/glossary/' | relative_url }}),
  [Appendix C]({{ '/en/appendices/appendix-c/' | relative_url }}), and the most
  relevant chapter or appendix when terminology, notation, or setup details
  have drifted

## What Makes This Book Different

- It compares multiple formal methods instead of treating one notation as the
  whole field.
- It explains both the mathematical promise and the engineering trade-offs.
- It is organized as a book first, with a learning path, chapter roles, and
  reference appendices, rather than as a loose collection of repository pages.
- It aims to support both a cover-to-cover read and later reuse as a desk
  reference.

## Table of Contents

{% include generated/toc-main-en.md %}

For hints, self-review checkpoints, and sample solution structures for the
end-of-chapter exercises, see
[Appendix D: Exercise Guides and Self-Review Frameworks]({{ '/en/appendices/appendix-d/' | relative_url }}).

## Appendices

On a second pass through the book, use Appendices C-F as the main reference
set: C for notation, D for exercise scaffolding, E for primary sources, and F
for AI-assisted working methods.

{% include generated/toc-appendices-en.md %}

## Using This Book as a Reference

After a first read, the book is designed to work as a reference in at least
three ways:

- return to the glossary and Appendix C when notation or terminology becomes
  unstable across projects
- use the method chapters to compare modeling styles before choosing a tool or
  specification approach
- use Chapters 11-13 and Appendix F when planning adoption, review workflows,
  or AI-assisted engineering practices

## License

Reader-facing content such as the main text, figures, and appendices is
distributed under `CC BY-NC-SA 4.0`. Code samples, tools, and build assets are
distributed under `Apache-2.0`.

<!-- markdownlint-disable MD034 -->
{% assign repo_url = site.github.repository_url | default: site.repository_url | default: site.repository.github | default: site.repository %}
{% if repo_url and repo_url != '' %}
{% unless repo_url contains 'http' %}
{% assign repo_url = 'https://github.com/' | append: repo_url %}
{% endunless %}
{% endif %}
{% assign repo_branch = site.repository_branch | default: 'main' %}

- [Full legal text of CC BY-NC-SA 4.0]({{ repo_url }}/blob/{{ repo_branch }}/LICENSE)
- [License scope]({{ repo_url }}/blob/{{ repo_branch }}/LICENSE-SCOPE.md)
- [Commercial licensing contact]({{ repo_url }}/blob/{{ repo_branch }}/COMMERCIAL.md)
- [Trademark policy]({{ repo_url }}/blob/{{ repo_branch }}/TRADEMARKS.md)
- [Third-party and upstream assets]({{ repo_url }}/blob/{{ repo_branch }}/THIRD_PARTY_NOTICES.md)
<!-- markdownlint-enable MD034 -->

## Contact

- ITDO Inc.
- Email: [knowledge@itdo.jp](mailto:knowledge@itdo.jp)
