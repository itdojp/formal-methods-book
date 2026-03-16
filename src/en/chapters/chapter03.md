# Chapter 3: Foundations of Specification

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter03.md`

This English page summarizes the scope and central examples of the Japanese
chapter. It is not yet a complete section-by-section translation.

## Why This Chapter Matters

Specifications are the bridge between intent and implementation. If they remain
ambiguous, incomplete, or inconsistent, later verification and testing inherit
that uncertainty. This chapter introduces the practical core of formal
specification work: removing ambiguity, stating contracts explicitly, and
capturing system-wide promises as invariants.

## What You Will Learn

- What specifications are, why they are layered, and how they evolve through a
  project lifecycle
- Why natural-language requirements are often structurally ambiguous and hard
  to verify
- How to write preconditions, postconditions, frame conditions, and exceptional
  postconditions as operation contracts
- How data invariants, business invariants, and system invariants constrain
  valid behavior
- How to judge whether a specification is complete enough to guide
  implementation, testing, and review

## Main Themes

- **Specifications are multi-layered**: they range from business intent to
  operational behavior and detailed data constraints.
- **Natural language alone is insufficient**: informal prose is accessible, but
  it often leaves key cases open to incompatible interpretations.
- **Contracts clarify responsibility**: preconditions state required inputs,
  postconditions state guarantees, and frame conditions state what does not
  change.
- **Invariants encode persistent promises**: they capture the conditions that
  must survive every valid operation.
- **Completeness matters**: a usable specification must cover normal behavior,
  error cases, relations among operations, and relevant non-functional
  constraints.

## Representative Example

The chapter develops a stack specification in detail. It covers the state
model, the core operations (`create`, `push`, `pop`, `top`, `isEmpty`, and
`size`), error handling, relationships among operations, performance
expectations, and concurrency considerations. The example shows how an informal
data structure can be turned into a complete, reviewable contract.

## How This Chapter Connects Forward

Chapter 3 completes the conceptual foundation for the method chapters. Alloy,
Z notation, CSP, and TLA+ all rely on the same discipline introduced here:
make assumptions explicit, define valid states, describe allowed transitions,
and check that important properties continue to hold.
