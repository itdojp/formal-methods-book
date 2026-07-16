---
layout: book
title: "Glossary"
locale: "en"
lang: "en"
source_path: "src/en/glossary/index.md"
translation_status: "partial"
translation_source_commit: "5b852a65db6c70440b98a6648136fd5c55e00e7a"
translation_reviewed_at: "2026-07-16"
translation_tracking_issue: "https://github.com/itdojp/formal-methods-book/issues/328"
---
# Glossary

> **Translation status: Partial.** Reviewed against Japanese source commit [`5b852a65db6c`](https://github.com/itdojp/formal-methods-book/commit/5b852a65db6c70440b98a6648136fd5c55e00e7a) on 2026-07-16.
> Some content, headings, examples, tables, or references remain partially synchronized. [Track the remaining work](https://github.com/itdojp/formal-methods-book/issues/328).

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
- **DTMC / CTMC / MDP**: Discrete-time Markov chain, continuous-time Markov
  chain, and Markov decision process. In PRISM they respectively represent
  step probabilities, transition rates, and nondeterministic choices followed
  by probability distributions.
- **PCTL / CSL**: Temporal logics for probabilistic reachability, timing, and
  long-run properties. PCTL is a basis for reading DTMC / MDP properties, while
  CSL serves the corresponding role for CTMCs.
- **CI**: Continuous Integration. Automated validation gates used for pull
  requests, nightly checks, and release preparation.
- **HOL**: Higher-Order Logic. A family of logics used by systems such as
  Isabelle/HOL.
- **RMW**: Read-Modify-Write. A common concurrent update pattern that can lead
  to lost updates.

## A

<span id="glossary-abstraction" class="search-term-anchor" aria-hidden="true"></span>**Abstraction**: The act of omitting details in order to focus on the
properties relevant to reasoning or verification. A useful model is abstract
enough to be analyzable but concrete enough to preserve the question being
asked. See Chapters 3, 4, and 8.

<span id="glossary-attack-trace" class="search-term-anchor" aria-hidden="true"></span>**Attack trace**: A violating trace containing adversary knowledge, message operations, and protocol events. In tools such as Tamarin, it is the retained explanation for a falsified lemma. See Chapter 13 and Appendix C.

<span id="glossary-alloy" class="search-term-anchor" aria-hidden="true"></span>**Alloy**: A representative lightweight formal-methods tool. It combines a
relational modeling language with an analyzer that searches for counterexamples.
See Chapter 4.

<span id="glossary-apalache" class="search-term-anchor" aria-hidden="true"></span>**Apalache**: An SMT-based checker for TLA+ specifications. It is useful when
you want symbolic or bounded exploration in addition to TLC's explicit-state
model checking. See Chapters 7, 8, and Appendix B.

<span id="glossary-assume--assert--cover-rtl-formal" class="search-term-anchor" aria-hidden="true"></span>**Assume / assert / cover (RTL formal)**: `assume` restricts the environment
traces under analysis, `assert` states a property that must not fail on those
traces, and `cover` searches for one trace reaching a condition. Review
over-strong assumptions for vacuity, and do not interpret cover reachability as
a safety proof. See Chapter 8 and Appendix C.

<span id="glossary-assertion" class="search-term-anchor" aria-hidden="true"></span>**Assertion**: A statement of a property that should hold. In Alloy this is
expressed with `assert`; in program verification it can also mean an explicit
check embedded in an implementation. See Chapters 4 and 10.

## B

<span id="glossary-bdd-binary-decision-diagram" class="search-term-anchor" aria-hidden="true"></span>**BDD (Binary Decision Diagram)**: A data structure for representing Boolean
functions efficiently. It is used in symbolic model checking. See Chapter 8.

## C

<span id="glossary-cap-theorem" class="search-term-anchor" aria-hidden="true"></span>**CAP theorem**: In an asynchronous model that permits messages to be lost by
a network partition, linearizable consistency and availability for every
request to a non-failing node cannot both be guaranteed during that partition.
It is not a rule to choose one of three letters at all times. See Chapter 7 and
Appendix E.

<span id="glossary-completeness" class="search-term-anchor" aria-hidden="true"></span>**Completeness**: A metaproperty relating a deductive system to a semantics:
every formula valid in that semantics is derivable. Completeness of
first-order logic for its standard semantics must not be generalized without
qualification to higher-order logic or dependent type theory. See Chapter 9.

<span id="glossary-contract" class="search-term-anchor" aria-hidden="true"></span>**Contract**: An explicit statement of what must hold before an operation and
what is guaranteed after it. Contracts often make preconditions and
postconditions visible to both implementers and reviewers. See Chapters 3 and
10.

<span id="glossary-counterexample" class="search-term-anchor" aria-hidden="true"></span>**Counterexample**: A concrete execution, trace, or state assignment that
shows why a claimed property does not hold. In practice, counterexamples are
often the most valuable output of a verifier because they direct debugging and
model revision. See Chapters 4, 7, and 8.

<span id="glossary-csp-communicating-sequential-processes" class="search-term-anchor" aria-hidden="true"></span>**CSP (Communicating Sequential Processes)**: A framework for describing
concurrent systems as compositions of processes and communication events. See
Chapter 6.

<span id="glossary-ctl-computation-tree-logic" class="search-term-anchor" aria-hidden="true"></span>**CTL (Computation Tree Logic)**: A branching-time temporal logic used to
express reachability and branching properties. See Chapter 8.

<span id="glossary-curry-howard-correspondence" class="search-term-anchor" aria-hidden="true"></span>**Curry-Howard correspondence**: The view that propositions correspond to
types, and proofs correspond to programs. See Chapter 9.

## D

<span id="glossary-dafny" class="search-term-anchor" aria-hidden="true"></span>**Dafny**: A verification-oriented programming language and toolchain for
writing implementations together with contracts, invariants, and proofs. See
Chapters 9, 10, and 12.

<span id="glossary-dolevyao-adversary-model" class="search-term-anchor" aria-hidden="true"></span>**Dolev–Yao adversary model**: A symbolic network model in which an attacker can intercept, modify, replay, and compose messages and use known keys, but does not break cryptography without the needed key. Compromise and side channels require explicit modeling. See Chapter 13 and Appendix E.

<span id="glossary-deadlock" class="search-term-anchor" aria-hidden="true"></span>**Deadlock**: A state in which multiple processes wait on one another and no
further progress is possible. See Chapters 6 and 8.

## F

<span id="glossary-flp-impossibility-result" class="search-term-anchor" aria-hidden="true"></span>**FLP impossibility result**: Under complete asynchrony, deterministic
processes, and at most one crash-stop failure, no consensus protocol guarantees
termination in every admissible execution. Partial synchrony, failure
detectors, and randomization address the problem by changing assumptions. See
Chapter 7 and Appendix E.

<span id="glossary-fairness" class="search-term-anchor" aria-hidden="true"></span>**Fairness**: An assumption about action selection used when reasoning about
liveness. In TLA+, weak fairness rules out ignoring an action that remains
continuously enabled, while strong fairness also covers an action enabled
infinitely often. It is an assumption on behaviors, not a guarantee that the
implementation's scheduler is fair; an overly strong assumption can make a
liveness claim appear to hold only because of that assumption. See Chapter 7.

<span id="glossary-formal-specification" class="search-term-anchor" aria-hidden="true"></span>**Formal specification**: A mathematically precise description of required
system behavior. Its purpose is to reduce ambiguity, expose hidden assumptions,
and support systematic analysis. See Chapters 3-7.

## H

<span id="glossary-hoare-logic" class="search-term-anchor" aria-hidden="true"></span>**Hoare logic**: A logical system for reasoning about program correctness using
preconditions, commands, and postconditions. See Chapter 10.

<span id="glossary-hoare-triple" class="search-term-anchor" aria-hidden="true"></span>**Hoare triple**: An expression of the form `{P} S {Q}`, where `P` is a
precondition, `S` is a program fragment, and `Q` is a postcondition. See
Chapter 10.

## I

<span id="glossary-invariant" class="search-term-anchor" aria-hidden="true"></span>**Invariant**: A property that must always hold. In model checking, violations
are typically shown as counterexamples. See Chapters 3, 7, and 8.

<span id="glossary-isabellehol" class="search-term-anchor" aria-hidden="true"></span>**Isabelle/HOL**: A proof assistant centered on higher-order logic. It is often
used for mechanized proofs, proof documentation, and larger proof libraries.
See Chapters 9 and 10.

## K

<span id="glossary-k-induction" class="search-term-anchor" aria-hidden="true"></span>**K-induction**: A proof method combining finite base cases with an induction
step stating that if the property holds for `k` steps, it also holds at the
next step. Success is relative to initialization, the transition relation,
properties, assumptions, and engine configuration. See Chapter 8 and Appendix
C.

## L

<span id="glossary-lean-4" class="search-term-anchor" aria-hidden="true"></span>**Lean 4**: A proof assistant and programming language based on dependent type
theory. In this book, it is presented as an engineering option for maintainable
proof assets rather than as the only proof workflow. See Chapter 9 and
Appendix B.

<span id="glossary-liveness" class="search-term-anchor" aria-hidden="true"></span>**Liveness**: A property stating that “something good eventually happens.”
Liveness claims are often sensitive to assumptions such as fairness. See
Chapter 8.

<span id="glossary-ltl-linear-temporal-logic" class="search-term-anchor" aria-hidden="true"></span>**LTL (Linear Temporal Logic)**: A temporal logic for expressing properties
along a single line of time. See Chapters 7 and 8.

<span id="glossary-loop-invariant" class="search-term-anchor" aria-hidden="true"></span>**Loop invariant**: A condition that remains true during every iteration of a
loop. It is central to proving partial and total correctness. See Chapter 10.

## M

<span id="glossary-model-checking" class="search-term-anchor" aria-hidden="true"></span>**Model checking**: A technique that explores the state space of a specified
model and checks selected properties. Exhaustiveness is relative to the model,
property, search configuration, fairness, and completion status; it is not a
claim about every behavior of the real system. See Chapter 8.

## P

<span id="glossary-partial-correctness" class="search-term-anchor" aria-hidden="true"></span>**Partial correctness**: The property that if a program terminates, the result
satisfies the required postcondition. It does not by itself prove termination.
See Chapter 10.

<span id="glossary-postcondition" class="search-term-anchor" aria-hidden="true"></span>**Postcondition**: A condition that must hold after an operation or program
fragment finishes, assuming the precondition held at the start. See Chapters 3
and 10.

<span id="glossary-precondition" class="search-term-anchor" aria-hidden="true"></span>**Precondition**: A condition that must hold before an operation or program
fragment starts for the promised result to be valid. See Chapters 3 and 10.

<span id="glossary-prime-notation-tla" class="search-term-anchor" aria-hidden="true"></span>**Prime notation (TLA+)**: Notation used inside an action to relate two states:
`x` is the current-state value and `x'` is the next-state value. It is distinct
from the LTL next-time operator `X` / `○`. See Chapter 7.

<span id="glossary-prism" class="search-term-anchor" aria-hidden="true"></span>**PRISM**: A model checker for probabilistic and quantitative properties of
DTMCs, CTMCs, and MDPs. Its results are relative to model assumptions,
schedulers, engines, and numerical precision; they do not establish that a
real-world probability model is valid. See Chapter 8 and Appendices B and E.

<span id="glossary-probabilistic-model-checking" class="search-term-anchor" aria-hidden="true"></span>**Probabilistic model checking**: Computing or checking reachability
probabilities, thresholds, steady-state probabilities, and expected rewards
over a transition model that contains probabilities or rates. It is distinct
from statistical model checking based only on sampled paths. See Chapter 8.

<span id="glossary-proof-assistant" class="search-term-anchor" aria-hidden="true"></span>**Proof assistant**: A software system that supports the construction and
checking of formal proofs. Examples discussed in this book include Rocq, Lean,
and Isabelle/HOL. See Chapters 9 and 12.

<span id="glossary-proof-obligation" class="search-term-anchor" aria-hidden="true"></span>**Proof obligation**: A logical claim that must be discharged for a proof or
verification argument to go through. Tools may generate proof obligations
automatically from contracts, invariants, or program structure. See Chapters 8,
9, and 10.

<span id="glossary-promela" class="search-term-anchor" aria-hidden="true"></span>**Promela**: The modeling language used by SPIN for concurrent systems. It is
suited to describing processes, communication, and interleavings. See Chapters
6 and 8.

## R

<span id="glossary-refinement" class="search-term-anchor" aria-hidden="true"></span>**Refinement**: The process of developing a concrete specification while
proving that, after applying a refinement mapping and hiding internal variables,
its behavior satisfies the abstract specification. Conceptually, the
implication runs as `ConcreteSpec => AbstractSpec`. See Chapters 3, 5, and 7.

<span id="glossary-reward-property" class="search-term-anchor" aria-hidden="true"></span>**Reward property**: A probabilistic property over values such as attempts,
time, energy, or cost attached to states or transitions. A reachability reward
can be infinite when the target is missed with positive probability. See
Chapter 8 and Appendix C.

<span id="glossary-rocq" class="search-term-anchor" aria-hidden="true"></span>**Rocq**: The proof assistant formerly known as Coq. It is based on type
theory and is used in this book as a representative environment for
mechanized proofs. See Chapters 9, 10, and Appendix E.

## S

<span id="glossary-soundness" class="search-term-anchor" aria-hidden="true"></span>**Soundness**: A metaproperty relating a deductive system to a semantics: every
derivable formula is valid in that semantics. The relevant logic and semantics
must be stated. See Chapter 9.

<span id="glossary-scheduler--adversary" class="search-term-anchor" aria-hidden="true"></span>**Scheduler / adversary**: A policy that resolves an MDP's nondeterministic
choices, potentially from the execution history. Best- and worst-case
probabilities and rewards depend on the scheduler class and the `min` / `max`
direction. See Chapter 8 and Appendix C.

<span id="glossary-statistical-model-checking" class="search-term-anchor" aria-hidden="true"></span>**Statistical model checking**: Approximating a property from randomly sampled
paths. The result depends on sample count, confidence, error width, and maximum
path length, and it does not automatically represent a worst-case MDP
scheduler. See Chapter 8.

<span id="glossary-safety" class="search-term-anchor" aria-hidden="true"></span>**Safety**: A property stating that “something bad never happens.” Such
properties are often expressed as invariants. See Chapter 8.

<span id="glossary-schema" class="search-term-anchor" aria-hidden="true"></span>**Schema**: In Z notation, a structured unit that groups declarations and
constraints. Schemas are used to describe states, operations, and related
conditions. See Chapter 5.

<span id="glossary-specification" class="search-term-anchor" aria-hidden="true"></span>**Specification**: A precise statement of what a system must do, independent of
how that behavior is implemented. In this book, specification is the bridge
between informal requirements and verifiable properties. See Chapters 3-7.

<span id="glossary-spin" class="search-term-anchor" aria-hidden="true"></span>**SPIN**: A model checker for concurrent systems centered on the Promela
language. See Chapters 6 and 8.

<span id="glossary-symbiyosys-sby" class="search-term-anchor" aria-hidden="true"></span>**SymbiYosys (sby)**: A front end for an open-source RTL formal flow centered
on Yosys. It connects BMC, prove, and cover tasks to engines and backends;
results are relative to the RTL, properties, assumptions, mode, depth, and
toolchain. See Chapter 8 and Appendices B and E.

<span id="glossary-state-space" class="search-term-anchor" aria-hidden="true"></span>**State space**: The set of states a system can take. Its size is a central
concern in verification. See Chapter 8.

<span id="glossary-state-explosion-problem" class="search-term-anchor" aria-hidden="true"></span>**State explosion problem**: The problem that the number of reachable states
can grow exponentially, making verification difficult. See Chapter 8.

<span id="glossary-state-transition" class="search-term-anchor" aria-hidden="true"></span>**State transition**: A change from one system state to another caused by an
operation, command, or event. State-transition thinking is central to TLA+,
model checking, and many verification arguments in this book. See Chapters 7,
8, and 10.

## T

<span id="glossary-tamarin-prover" class="search-term-anchor" aria-hidden="true"></span>**Tamarin Prover**: A symbolic security-protocol verifier using multiset-rewriting rules, facts, events, and trace lemmas under an active adversary. Results are relative to the equational theory, assumptions, lemmas, and proof configuration. See Chapter 13 and Appendices B and E.

<span id="glossary-tla" class="search-term-anchor" aria-hidden="true"></span>**TLA+**: A specification language for distributed and concurrent systems. It
uses actions to relate current and next states and temporal formulas to describe
complete behaviors, normally in a stuttering-permitting form. Prime notation is
not the LTL next-time operator. See Chapter 7.

<span id="glossary-temporal-logic" class="search-term-anchor" aria-hidden="true"></span>**Temporal logic**: A family of logics used to describe how properties evolve
over time. LTL and CTL are representative examples; in TLA+, `[]`, `<>`, and
`~>` describe behavior properties, while prime notation belongs to actions.
See Chapters 7 and 8.

<span id="glossary-theorem-proving" class="search-term-anchor" aria-hidden="true"></span>**Theorem proving**: A style of verification that establishes correctness by
constructing a proof rather than exhaustively exploring a state space. See
Chapter 9.

<span id="glossary-tlc" class="search-term-anchor" aria-hidden="true"></span>**TLC**: An explicit-state model checker that enumerates reachable states of a
concrete finite model of a TLA+ specification. TLA+ has no conventional static
type system; predicates commonly named `TypeOK` or `TypeInvariant` assert that
values belong to expected sets. Results depend on the `.cfg`, properties,
fairness, state constraints, and completion status. See Chapters 7 and 8.

<span id="glossary-trusted-kernel" class="search-term-anchor" aria-hidden="true"></span>**Trusted kernel**: The small core that checks proof terms under the
foundational logic and current environment. The wider trusted computing base
can also include added axioms, unfinished holes, unchecked solver paths,
extraction, and code generation. See Chapter 9.

<span id="glossary-total-correctness" class="search-term-anchor" aria-hidden="true"></span>**Total correctness**: The claim that a program not only satisfies the required
postcondition when it terminates, but also does terminate. See Chapter 10.

<span id="glossary-trace" class="search-term-anchor" aria-hidden="true"></span>**Trace**: A sequence of state transitions. Counterexamples are often presented
as traces; security-protocol verification may present one as an attack trace
that includes adversary operations. See Chapters 8 and 13.

<span id="glossary-type-theory" class="search-term-anchor" aria-hidden="true"></span>**Type theory**: A logical foundation used by many proof assistants, where
types and propositions are closely connected. It is central to Rocq, Lean, and
the discussion in Chapter 9. See Chapter 9.

## V

<span id="glossary-vacuity" class="search-term-anchor" aria-hidden="true"></span>**Vacuity**: A property can hold trivially because an over-strong assumption
or unreachable premise removed the executions that mattered, rather than
because the intended behavior was established. Assumption review and
meaningful cover targets help expose this failure mode. See Chapter 8 and
Appendix C.

<span id="glossary-verification-condition" class="search-term-anchor" aria-hidden="true"></span>**Verification condition**: A logical obligation generated from a program or
specification that must be proved for a correctness claim to hold. See Chapter
10.

## Z

<span id="glossary-z-notation" class="search-term-anchor" aria-hidden="true"></span>**Z notation**: A state-based formal specification language that uses schemas
to describe states and operations. See Chapter 5.

## Related Links

- [Appendix A: Mathematics Refresher]({{ '/en/appendices/appendix-a/' | relative_url }})
- [Appendix B: Tool Setup and Verification Quick Start]({{ '/en/appendices/appendix-b/' | relative_url }})
- [Appendix C: Notation Cross-Reference]({{ '/en/appendices/appendix-c/' | relative_url }})
- [Appendix E: References and Further Reading Paths]({{ '/en/appendices/appendix-e/' | relative_url }})
