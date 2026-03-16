# Chapter 1: Why Formal Methods Matter

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter01.md`

This English page summarizes the intent, structure, and representative examples
of the Japanese chapter. It is not yet a paragraph-by-paragraph translation.

## Why This Chapter Matters

Modern software is deeply interconnected, socially embedded, and difficult to
reason about by intuition alone. As the number of states, interactions, and
failure modes grows, empirical techniques such as testing and review remain
essential but cannot provide exhaustive assurance on their own. This chapter
explains why formal methods matter before introducing any specific notation.

## What You Will Learn

- Why increasing system complexity creates behaviors that are hard to predict
  or validate empirically
- Why reliability is both a technical concern and a social obligation,
  especially in safety- and mission-critical domains
- What recurring patterns appear in major failures such as Ariane 5,
  Therac-25, and later large-scale software incidents
- Where test-driven development, code review, and static analysis help, and
  where their coverage stops
- What formal methods add through precise specification, early verification,
  automation, and reusable evidence

## Main Themes

- **Complexity creates blind spots**: combinatorial growth and emergent
  behavior make informal reasoning fragile.
- **Reliability is accountable**: software failures can become operational,
  medical, financial, or legal incidents.
- **Conventional quality practices are necessary but incomplete**: they reduce
  risk, but they do not eliminate ambiguity or exhaust large state spaces.
- **Formal methods move assurance earlier**: mathematical models and proofs can
  expose defects during requirements and design, before implementation cost
  rises.
- **Verification artifacts become assets**: explicit specifications and checked
  arguments can be reused across review, maintenance, and compliance work.

## Representative Cases

- **Ariane 5** is used to discuss how reused assumptions and insufficiently
  explicit specifications can become catastrophic in a new context.
- **Therac-25** illustrates the cost of weak specification and verification in
  a safety-critical medical system.
- **Modern incidents** show that the same structural problems remain relevant:
  ambiguity, unmodeled assumptions, and overconfidence in partial checks.

## How This Chapter Connects Forward

Chapter 1 provides the motivation for the rest of the book. Chapter 2 shows
that the mathematical ideas behind formal methods are already present in
everyday programming. Chapter 3 then turns those ideas into explicit
specifications with contracts and invariants. The later chapters build on this
foundation with concrete methods, tools, and industrial practices.
