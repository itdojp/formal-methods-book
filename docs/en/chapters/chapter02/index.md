---
layout: book
title: "Chapter 2: Bridging Mathematics and Programs"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter02.md"
---
# Chapter 2: Bridging Mathematics and Programs

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter02.md`

This English page summarizes the core ideas and learning goals of the Japanese
chapter. It is not yet a full translation.

## Why This Chapter Matters

Formal methods are easier to learn when they are presented as an extension of
concepts that software engineers already use. Variables, functions, data
structures, type systems, control flow, and error handling all have a
mathematical structure. This chapter makes that structure explicit and
establishes the vocabulary needed for the rest of the book.

## What You Will Learn

- How common programming constructs can be interpreted in terms of sets,
  relations, functions, and logic
- How to define correctness as a relationship between a specification and an
  implementation
- Why partial correctness, total correctness, and invariants matter when
  reasoning about software behavior
- How predicate logic expresses constraints, control conditions, and proof
  obligations
- How states, transitions, and interleavings model dynamic and concurrent
  systems

## Main Themes

- **Programming already uses mathematics**: formal methods do not introduce a
  separate world so much as they make existing structure precise.
- **Specifications define correctness**: software is not "correct" in the
  abstract; it is correct relative to an explicit contract.
- **Sets, relations, and functions are foundational**: they provide a compact
  language for describing data, connectivity, and transformation.
- **Logic supports explanation and proof**: conditions, implications, and
  quantified properties make reasoning about behavior auditable.
- **State models make change analyzable**: transitions, invariants, and
  concurrency models expose where defects and race conditions come from.

## Representative Concepts and Exercises

- Set-based modeling of entities, attributes, and memberships
- Relations and functions as a basis for access control, lookup, and mapping
- Logical conditions behind branching, validation, and program proofs
- State-transition views of mutable systems, including concurrent execution and
  interleaving
- Preparatory exercises for Alloy, Z, CSP, and TLA+ in the later chapters

## How This Chapter Connects Forward

Chapter 2 supplies the mathematical toolkit for the remainder of Part I and
for the method chapters that follow. Chapter 3 uses these concepts to write
unambiguous specifications with preconditions, postconditions, and invariants.
Chapters 4 through 7 then reuse the same ideas in concrete form across Alloy,
Z notation, CSP, and TLA+.
