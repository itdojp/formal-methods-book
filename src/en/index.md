# Formal Methods: Foundations and Applications

An integrated introduction to specification, model checking, theorem proving,
and program verification.

## Learning Outcomes

- Understand why formal methods are needed, where they are effective, and how
  to reason about their benefits, limits, and cost.
- Compare representative specification languages and verification techniques,
  including Alloy, Z, CSP, TLA+, model checking, and theorem proving.
- Practice the end-to-end flow of writing small specifications, running tools,
  and interpreting verification results on compact examples.
- Apply formal-methods thinking incrementally in reviews, test design,
  documentation, and architecture discussions even when full adoption is not
  realistic.

## How to Use This Book

- If you are new to formal methods, start with
  [Introduction]({{ '/en/introduction/' | relative_url }}) and read Part I in
  order before moving to the individual methods in Part II.
- If you already care about a specific technique such as Alloy or TLA+, start
  from that chapter and use Chapters 1 and 2 to fill in the background and the
  comparison points.
- If your main interest is verification, use Part III as the spine of your
  reading and move backward or forward as needed.
- If you are considering adoption in practice, focus on Part IV together with
  the related foundational chapters.

## Intended Audience

This book is written for the following readers:

- **Software engineers and architects** who want more rigorous design and
  specification practices
- **Quality assurance and test engineers** who want to understand mathematical
  verification in addition to conventional testing
- **Engineers working on safety-, security-, or reliability-critical systems**
- **Students and researchers in computer science** who want to connect theory
  and practice

## Prerequisites

To get the most out of this book, you should already be comfortable with the
following basics:

- **Programming**: basic coding experience, fundamental data structures and
  algorithms, and the essentials of structured or object-oriented development
- **Mathematics**: high-school-level sets, logic, and functions, plus a basic
  feel for discrete mathematics and mathematical reasoning
- **Software engineering**: requirements, design, testing, and the software
  lifecycle

The book uses mathematical notation throughout, but it explains the required
concepts from the ground up. Advanced mathematics is not required.

## Estimated Time

Typical study time depends on your background and on how deeply you work
through the exercises:

- Reading the main text: about 8 to 16 hours
- Reading plus exercises and tool execution: about 25 to 40 hours

We recommend studying chapter by chapter instead of treating the book as a
single uninterrupted read.

## English Edition Status

The English edition is being expanded incrementally. The front matter, glossary,
and supporting pages are available in English, while chapter and appendix bodies
still keep a one-to-one correspondence with the Japanese edition as translation
work proceeds.

## Table of Contents

- [Introduction]({{ '/en/introduction/' | relative_url }})
- [Glossary]({{ '/en/glossary/' | relative_url }})

### Part I: Foundations

- [Chapter 1: Why Formal Methods Matter]({{ '/en/chapters/chapter01/' | relative_url }})
- [Chapter 2: Bridging Mathematics and Programs]({{ '/en/chapters/chapter02/' | relative_url }})
- [Chapter 3: Foundations of Specification]({{ '/en/chapters/chapter03/' | relative_url }})

### Part II: Methods

- [Chapter 4: Introduction to Lightweight Formal Methods — Specification with Alloy]({{ '/en/chapters/chapter04/' | relative_url }})
- [Chapter 5: State-Based Specification — Fundamentals of Z Notation]({{ '/en/chapters/chapter05/' | relative_url }})
- [Chapter 6: Process-Centric Specification — Concurrency with CSP]({{ '/en/chapters/chapter06/' | relative_url }})
- [Chapter 7: Specifying Time — Introduction to TLA+]({{ '/en/chapters/chapter07/' | relative_url }})

### Part III: Verification

- [Chapter 8: Introduction to Model Checking]({{ '/en/chapters/chapter08/' | relative_url }})
- [Chapter 9: Fundamentals of Theorem Proving]({{ '/en/chapters/chapter09/' | relative_url }})
- [Chapter 10: Program Verification]({{ '/en/chapters/chapter10/' | relative_url }})

### Part IV: Practice

- [Chapter 11: Integrating Formal Methods into Development Processes]({{ '/en/chapters/chapter11/' | relative_url }})
- [Chapter 12: Tools and Automation]({{ '/en/chapters/chapter12/' | relative_url }})
- [Chapter 13: Case Studies]({{ '/en/chapters/chapter13/' | relative_url }})

For hints, grading viewpoints, and sample solution structure for the
end-of-chapter exercises, see
[Appendix D: Exercise Hints and Solutions]({{ '/en/appendices/appendix-d/' | relative_url }}).

## Appendices

- [Appendix A: Mathematics Refresher]({{ '/en/appendices/appendix-a/' | relative_url }})
- [Appendix B: Tool Installation Guide]({{ '/en/appendices/appendix-b/' | relative_url }})
- [Appendix C: Notation Cross-Reference]({{ '/en/appendices/appendix-c/' | relative_url }})
- [Appendix D: Exercise Hints and Solutions]({{ '/en/appendices/appendix-d/' | relative_url }})
- [Appendix E: References and Web Resources]({{ '/en/appendices/appendix-e/' | relative_url }})
- [Appendix F: Practical Guide to AI Assistance]({{ '/en/appendices/appendix-f/' | relative_url }})
- [Afterword]({{ '/en/afterword/' | relative_url }})

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

---

**Author:** Kazuhiko Ota (ITDO Inc.)  
**Version:** 1.0.0  
**Last updated:** {{ site.time | date: '%Y-%m-%d' }}  
**GitHub Pages:** automatic deployment enabled
