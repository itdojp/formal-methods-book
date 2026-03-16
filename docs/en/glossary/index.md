---
layout: book
title: "Glossary"
locale: "en"
lang: "en"
source_path: "src/en/glossary/index.md"
---
# Glossary

This glossary collects technical terms and abbreviations that appear repeatedly
throughout the book. The definitions prioritize the way each term is used in
this book. When stricter distinctions matter, refer to the appendices or to
primary sources.

## 0) Acronyms

- **SAT**: Satisfiability. The satisfiability problem for propositional logic.
  Some tools such as Alloy reduce internal checks to SAT solving.
- **SMT**: Satisfiability Modulo Theories. A framework that combines
  satisfiability checking with theories such as equality, arithmetic, and
  arrays.
- **LTL / CTL**: Linear Temporal Logic and Computation Tree Logic. Temporal
  logics used to describe properties in model checking.
- **CI**: Continuous Integration. Automated validation gates used for pull
  requests, nightly checks, and release preparation.
- **RMW**: Read-Modify-Write. A common concurrent update pattern that can lead
  to lost updates.

## A

**Alloy**: A representative lightweight formal-methods tool. It combines a
relational modeling language with an analyzer that searches for counterexamples.
See Chapter 4.

**Assertion**: A statement of a property that should hold. In Alloy this is
expressed with `assert`; in program verification it can also mean an explicit
check embedded in an implementation. See Chapters 4 and 10.

## B

**BDD (Binary Decision Diagram)**: A data structure for representing Boolean
functions efficiently. It is used in symbolic model checking. See Chapter 8.

## C

**CSP (Communicating Sequential Processes)**: A framework for describing
concurrent systems as compositions of processes and communication events. See
Chapter 6.

**CTL (Computation Tree Logic)**: A branching-time temporal logic used to
express reachability and branching properties. See Chapter 8.

**Curry-Howard correspondence**: The view that propositions correspond to
types, and proofs correspond to programs. See Chapter 9.

## D

**Deadlock**: A state in which multiple processes wait on one another and no
further progress is possible. See Chapters 6 and 8.

## F

**Fairness**: An assumption about scheduling or progress used when reasoning
about liveness. If it is too strong, a property may appear to hold only because
of the assumption. See Chapter 7.

## H

**Hoare logic**: A logical system for reasoning about program correctness using
preconditions, commands, and postconditions. See Chapter 10.

**Hoare triple**: An expression of the form `{P} S {Q}`, where `P` is a
precondition, `S` is a program fragment, and `Q` is a postcondition. See
Chapter 10.

## I

**Invariant**: A property that must always hold. In model checking, violations
are typically shown as counterexamples. See Chapters 3, 7, and 8.

## L

**Liveness**: A property stating that “something good eventually happens.”
Liveness claims are often sensitive to assumptions such as fairness. See
Chapter 8.

**LTL (Linear Temporal Logic)**: A temporal logic for expressing properties
along a single line of time. See Chapters 7 and 8.

**Loop invariant**: A condition that remains true during every iteration of a
loop. It is central to proving partial and total correctness. See Chapter 10.

## M

**Model checking**: A technique that explores a system's state space and
automatically determines whether a property holds. See Chapter 8.

## S

**Safety**: A property stating that “something bad never happens.” Such
properties are often expressed as invariants. See Chapter 8.

**SPIN**: A model checker for concurrent systems centered on the Promela
language. See Chapters 6 and 8.

**State space**: The set of states a system can take. Its size is a central
concern in verification. See Chapter 8.

**State explosion problem**: The problem that the number of reachable states
can grow exponentially, making verification difficult. See Chapter 8.

## T

**TLA+**: A specification language for distributed and concurrent systems based
on state transitions and temporal logic. See Chapter 7.

**TLC**: The model checker for TLA+ specifications. See Chapters 7 and 8.

**Trace**: A sequence of state transitions. Counterexamples are often presented
as traces. See Chapter 8.

## Z

**Z notation**: A state-based formal specification language that uses schemas
to describe states and operations. See Chapter 5.

## Related Links

- [Appendix A: Mathematics Refresher]({{ '/en/appendices/appendix-a/' | relative_url }})
- [Appendix C: Notation Cross-Reference]({{ '/en/appendices/appendix-c/' | relative_url }})
