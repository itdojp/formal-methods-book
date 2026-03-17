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

## What This Book Delivers

- A practical map of the formal-methods landscape, from foundational concepts
  to adoption in real development work
- A comparative treatment of representative approaches, including Alloy, Z,
  CSP, TLA+, model checking, theorem proving, and program verification
- Small but concrete examples that show how specifications, properties, and
  verification results fit together
- A decision-oriented view of where formal methods help, where they are costly,
  and how to introduce them without disrupting an entire organization

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

## Suggested Reading Paths

- **First read**: start with
  [Introduction]({{ '/en/introduction/' | relative_url }}) and read Parts I and
  II in order before moving to the verification chapters
- **Architecture and design focus**: read Chapters 1-4, Chapter 7, Chapter 11,
  and Chapter 13
- **Verification focus**: read Chapters 1-3, then use Chapters 8-10 as the
  backbone of the book
- **Adoption focus**: read Chapters 1, 3, 11, 12, and 13 together with the
  relevant appendices

## What Makes This Book Different

- It compares multiple formal methods instead of treating one notation as the
  whole field.
- It explains both the mathematical promise and the engineering trade-offs.
- It is organized as a book first, with a learning path, chapter roles, and
  reference appendices, rather than as a loose collection of repository pages.
- It aims to support both a cover-to-cover read and later reuse as a desk
  reference.

## Table of Contents

- [Introduction]({{ '/en/introduction/' | relative_url }})
- [Glossary]({{ '/en/glossary/' | relative_url }})

### Part I: Foundations

- establishes why formal methods matter, where intuition breaks down, and what
  conceptual tools the rest of the book depends on
- [Chapter 1: Why Formal Methods Matter]({{ '/en/chapters/chapter01/' | relative_url }})
- [Chapter 2: Bridging Mathematics and Programs]({{ '/en/chapters/chapter02/' | relative_url }})
- [Chapter 3: Foundations of Specification]({{ '/en/chapters/chapter03/' | relative_url }})

### Part II: Methods

- introduces representative specification styles so that readers can compare
  modeling choices rather than memorize isolated syntax
- [Chapter 4: Introduction to Lightweight Formal Methods — Specification with Alloy]({{ '/en/chapters/chapter04/' | relative_url }})
- [Chapter 5: State-Based Specification — Fundamentals of Z Notation]({{ '/en/chapters/chapter05/' | relative_url }})
- [Chapter 6: Process-Centric Specification — Concurrency with CSP]({{ '/en/chapters/chapter06/' | relative_url }})
- [Chapter 7: Specifying Time — Introduction to TLA+]({{ '/en/chapters/chapter07/' | relative_url }})

### Part III: Verification

- explains how properties are checked, proved, or derived, and where each
  verification style provides practical value
- [Chapter 8: Introduction to Model Checking]({{ '/en/chapters/chapter08/' | relative_url }})
- [Chapter 9: Fundamentals of Theorem Proving]({{ '/en/chapters/chapter09/' | relative_url }})
- [Chapter 10: Program Verification]({{ '/en/chapters/chapter10/' | relative_url }})

### Part IV: Practice

- moves from theory to engineering practice: process integration, tools,
  automation, and case studies
- [Chapter 11: Integrating Formal Methods into Development Processes]({{ '/en/chapters/chapter11/' | relative_url }})
- [Chapter 12: Tools and Automation]({{ '/en/chapters/chapter12/' | relative_url }})
- [Chapter 13: Case Studies]({{ '/en/chapters/chapter13/' | relative_url }})

For hints, self-review checkpoints, and sample solution structures for the
end-of-chapter exercises, see
[Appendix D: Exercise Hints and Solutions]({{ '/en/appendices/appendix-d/' | relative_url }}).

## Appendices

On a second pass through the book, use Appendices C-F as the main reference
set: C for notation, D for exercise scaffolding, E for primary sources, and F
for AI-assisted working methods.

- [Appendix A: Mathematics Refresher]({{ '/en/appendices/appendix-a/' | relative_url }})
- [Appendix B: Tool Installation Guide]({{ '/en/appendices/appendix-b/' | relative_url }})
- [Appendix C: Notation Cross-Reference]({{ '/en/appendices/appendix-c/' | relative_url }})
- [Appendix D: Exercise Hints and Solutions]({{ '/en/appendices/appendix-d/' | relative_url }})
- [Appendix E: References and Further Reading Paths]({{ '/en/appendices/appendix-e/' | relative_url }})
- [Appendix F: Practical Playbook for AI-Assisted Formal Methods]({{ '/en/appendices/appendix-f/' | relative_url }})
- [Afterword]({{ '/en/afterword/' | relative_url }})

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
