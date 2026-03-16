# Chapter 4: Introduction to Lightweight Formal Methods: Specification with Alloy

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter04.md`

This English page summarizes the structure and learning goals of the Japanese
chapter. It is not yet a full translation.

## Why This Method Matters

Alloy is often the most accessible entry point into formal methods because it
focuses on bounded exploration and counterexample discovery rather than full
proof from the start. That makes it useful during requirements and design work,
when teams need to find structural mistakes early and cheaply.

## Core Ideas

- **Lightweight does not mean weak**: Alloy trades full general proofs for
  rapid, bounded analysis that is highly effective at exposing design defects.
- **Relations are the core modeling primitive**: systems are described as sets
  of atoms and relations among them, rather than as code-level objects.
- **Facts, predicates, assertions, and scopes play different roles**: facts
  constrain all instances, predicates capture reusable conditions, assertions
  express expected properties, and scopes define the bounded search space.
- **Counterexamples are a design tool**: when an assertion fails, the returned
  instance helps explain exactly which assumption is wrong or incomplete.

## What This Chapter Covers

- The philosophy of lightweight formal methods and bounded checking
- Relational modeling with signatures, fields, multiplicities, and facts
- Basic Alloy models such as an address book and progressively richer
  structural constraints
- Property description with logic, quantifiers, set operators, and temporal
  viewpoints
- Practical verification with Alloy Analyzer, including `run`, `assert`, and
  `check`

## Representative Models

The Japanese chapter develops examples such as an address book, access control
for an email system, inventory management for an online bookstore, and leader
election in a distributed system. Together, these examples show where Alloy is
effective: expressing structural constraints, finding missing assumptions, and
checking whether expected properties really follow from the model.

## When to Use Alloy

Alloy is a good fit when you want to reason about structure, consistency, and
small counterexamples quickly. It is especially useful for data models,
permissions, configuration rules, protocol structure, and early-stage design
alternatives. When a property requires unbounded proof, richer temporal
arguments, or implementation-level verification, later chapters cover methods
that go further.

## Relationship to Other Chapters

Chapter 4 is the first method chapter, so it turns the foundational ideas from
Chapters 1 through 3 into executable modeling practice. Chapter 5 shifts to
state-based specification with Z notation, Chapter 6 focuses on concurrency
with CSP, and Chapter 7 extends the discussion to temporal behavior with TLA+.
