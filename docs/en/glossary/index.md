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

## How to Use This Glossary

This glossary is designed for fast re-entry. If you return to the book after a
break, use it to recover the meaning of a term, re-establish the distinction
between similar ideas, and jump back to the relevant chapter. Definitions are
kept short on purpose. When the technical boundary matters, the listed chapter
should be treated as the primary explanation. Use Appendix B when the term is
mainly about tool setup, Appendix C when the issue is notation, and Appendix E
when you need primary sources.

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
- **HOL**: Higher-Order Logic. A family of logics used by systems such as
  Isabelle/HOL.
- **RMW**: Read-Modify-Write. A common concurrent update pattern that can lead
  to lost updates.

## A

**Abstraction**: The act of omitting details in order to focus on the
properties relevant to reasoning or verification. A useful model is abstract
enough to be analyzable but concrete enough to preserve the question being
asked. See Chapters 3, 4, and 8.

**Alloy**: A representative lightweight formal-methods tool. It combines a
relational modeling language with an analyzer that searches for counterexamples.
See Chapter 4.

**Apalache**: An SMT-based checker for TLA+ specifications. It is useful when
you want symbolic or bounded exploration in addition to TLC's explicit-state
model checking. See Chapters 7, 8, and Appendix B.

**Assertion**: A statement of a property that should hold. In Alloy this is
expressed with `assert`; in program verification it can also mean an explicit
check embedded in an implementation. See Chapters 4 and 10.

## B

**BDD (Binary Decision Diagram)**: A data structure for representing Boolean
functions efficiently. It is used in symbolic model checking. See Chapter 8.

## C

**Contract**: An explicit statement of what must hold before an operation and
what is guaranteed after it. Contracts often make preconditions and
postconditions visible to both implementers and reviewers. See Chapters 3 and
10.

**Counterexample**: A concrete execution, trace, or state assignment that
shows why a claimed property does not hold. In practice, counterexamples are
often the most valuable output of a verifier because they direct debugging and
model revision. See Chapters 4, 7, and 8.

**CSP (Communicating Sequential Processes)**: A framework for describing
concurrent systems as compositions of processes and communication events. See
Chapter 6.

**CTL (Computation Tree Logic)**: A branching-time temporal logic used to
express reachability and branching properties. See Chapter 8.

**Curry-Howard correspondence**: The view that propositions correspond to
types, and proofs correspond to programs. See Chapter 9.

## D

**Dafny**: A verification-oriented programming language and toolchain for
writing implementations together with contracts, invariants, and proofs. See
Chapters 9, 10, and 12.

**Deadlock**: A state in which multiple processes wait on one another and no
further progress is possible. See Chapters 6 and 8.

## F

**Fairness**: An assumption about scheduling or progress used when reasoning
about liveness. If it is too strong, a property may appear to hold only because
of the assumption. See Chapter 7.

**Formal specification**: A mathematically precise description of required
system behavior. Its purpose is to reduce ambiguity, expose hidden assumptions,
and support systematic analysis. See Chapters 3-7.

## H

**Hoare logic**: A logical system for reasoning about program correctness using
preconditions, commands, and postconditions. See Chapter 10.

**Hoare triple**: An expression of the form `{P} S {Q}`, where `P` is a
precondition, `S` is a program fragment, and `Q` is a postcondition. See
Chapter 10.

## I

**Invariant**: A property that must always hold. In model checking, violations
are typically shown as counterexamples. See Chapters 3, 7, and 8.

**Isabelle/HOL**: A proof assistant centered on higher-order logic. It is often
used for mechanized proofs, proof documentation, and larger proof libraries.
See Chapters 9 and 10.

## L

**Lean 4**: A proof assistant and programming language based on dependent type
theory. In this book, it is presented as an engineering option for maintainable
proof assets rather than as the only proof workflow. See Chapter 9 and
Appendix B.

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

## P

**Partial correctness**: The property that if a program terminates, the result
satisfies the required postcondition. It does not by itself prove termination.
See Chapter 10.

**Postcondition**: A condition that must hold after an operation or program
fragment finishes, assuming the precondition held at the start. See Chapters 3
and 10.

**Precondition**: A condition that must hold before an operation or program
fragment starts for the promised result to be valid. See Chapters 3 and 10.

**Proof assistant**: A software system that supports the construction and
checking of formal proofs. Examples discussed in this book include Rocq, Lean,
and Isabelle/HOL. See Chapters 9 and 12.

**Proof obligation**: A logical claim that must be discharged for a proof or
verification argument to go through. Tools may generate proof obligations
automatically from contracts, invariants, or program structure. See Chapters 8,
9, and 10.

**Promela**: The modeling language used by SPIN for concurrent systems. It is
suited to describing processes, communication, and interleavings. See Chapters
6 and 8.

## R

**Refinement**: The process of turning an abstract specification into a more
concrete design or implementation while preserving the essential properties of
the original specification. See Chapters 3, 5, and 10.

**Rocq**: The proof assistant formerly known as Coq. It is based on type
theory and is used in this book as a representative environment for
mechanized proofs. See Chapters 9, 10, and Appendix E.

## S

**Safety**: A property stating that “something bad never happens.” Such
properties are often expressed as invariants. See Chapter 8.

**Schema**: In Z notation, a structured unit that groups declarations and
constraints. Schemas are used to describe states, operations, and related
conditions. See Chapter 5.

**Specification**: A precise statement of what a system must do, independent of
how that behavior is implemented. In this book, specification is the bridge
between informal requirements and verifiable properties. See Chapters 3-7.

**SPIN**: A model checker for concurrent systems centered on the Promela
language. See Chapters 6 and 8.

**State space**: The set of states a system can take. Its size is a central
concern in verification. See Chapter 8.

**State explosion problem**: The problem that the number of reachable states
can grow exponentially, making verification difficult. See Chapter 8.

**State transition**: A change from one system state to another caused by an
operation, command, or event. State-transition thinking is central to TLA+,
model checking, and many verification arguments in this book. See Chapters 7,
8, and 10.

## T

**TLA+**: A specification language for distributed and concurrent systems based
on state transitions and temporal logic. See Chapter 7.

**Temporal logic**: A family of logics used to describe how properties evolve
over time. LTL and CTL are representative examples discussed in this book. See
Chapters 7 and 8.

**Theorem proving**: A style of verification that establishes correctness by
constructing a proof rather than exhaustively exploring a state space. See
Chapter 9.

**TLC**: The model checker for TLA+ specifications. See Chapters 7 and 8.

**Total correctness**: The claim that a program not only satisfies the required
postcondition when it terminates, but also does terminate. See Chapter 10.

**Trace**: A sequence of state transitions. Counterexamples are often presented
as traces. See Chapter 8.

**Type theory**: A logical foundation used by many proof assistants, where
types and propositions are closely connected. It is central to Rocq, Lean, and
the discussion in Chapter 9. See Chapter 9.

## V

**Verification condition**: A logical obligation generated from a program or
specification that must be proved for a correctness claim to hold. See Chapter
10.

## Z

**Z notation**: A state-based formal specification language that uses schemas
to describe states and operations. See Chapter 5.

## Related Links

- [Appendix A: Mathematics Refresher]({{ '/en/appendices/appendix-a/' | relative_url }})
- [Appendix B: Tool Setup and Verification Quick Start]({{ '/en/appendices/appendix-b/' | relative_url }})
- [Appendix C: Notation Cross-Reference]({{ '/en/appendices/appendix-c/' | relative_url }})
- [Appendix E: References and Further Reading Paths]({{ '/en/appendices/appendix-e/' | relative_url }})
