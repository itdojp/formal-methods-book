---
layout: book
title: "Chapter 7: Specifying Time: Introduction to TLA+"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter07.md"
---
# Chapter 7: Specifying Time: Introduction to TLA+

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter07.md`

This English page summarizes the main learning goals of the Japanese chapter.
It is not yet a full translation.

## Why This Method Matters

Distributed systems are hard because correctness depends on changing state over
time, partial failure, nondeterministic interleavings, and properties that must
hold across entire behaviors rather than in one snapshot. TLA+ addresses this
by combining state-transition modeling with temporal logic.

## Core Ideas

- **Behavior is a sequence of states**: TLA+ specifications describe how a
  system starts, how it can move, and which long-run properties must hold.
- **Actions describe change**: primed variables and action formulas make state
  updates explicit and analyzable.
- **Temporal logic distinguishes safety and liveness**: some properties say
  that "nothing bad happens," while others say that "something good eventually
  happens."
- **Fairness and refinement matter**: distributed algorithms often require
  assumptions about progress and about how abstract and concrete models relate.

## What This Chapter Covers

- The difficulty of reasoning about time, causality, and partial failure in
  distributed systems
- The TLA+ worldview of states, actions, temporal operators, and refinement
- Core specification structure with variables, `Init`, `Next`, frame
  conditions, and temporal properties
- Safety, liveness, fairness, and other temporal properties expressed in logic
- Practical model checking with TLC, including error traces and state-space
  control

## Representative Application

The Japanese chapter connects TLA+ to distributed consensus, including Raft.
It explains how leader election, log replication, safety guarantees, failure
scenarios, and progress properties can be expressed as a formal specification
and then checked with TLC.

## When to Use TLA+

TLA+ is a strong choice when the critical questions are temporal and systemic:
ordering constraints, distributed coordination, retries, failover, eventual
progress, and consistency under concurrency. It is particularly useful for
protocols, replicated services, and algorithms whose correctness depends on
long-running behavior rather than on one operation in isolation.

## Relationship to Other Chapters

Chapter 7 extends the method sequence from structural modeling and state-based
specification to explicit reasoning about time and behavior. Chapter 8 then
builds on this mindset when introducing model checking more directly, while the
later case-study chapters revisit the same kinds of system-level concerns in
practice.
