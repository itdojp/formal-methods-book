# Chapter 5: State-Based Specification: Foundations of Z Notation

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter05.md`

This English page summarizes the scope and central concepts of the Japanese
chapter. It is not yet a complete translation.

## Why This Method Matters

Z notation is a classic state-based formal specification language. It is useful
when a system must be described in terms of state, invariants, and operations
with mathematically explicit preconditions and postconditions. This makes Z a
strong fit for systems where consistency and controlled state change are the
main concerns.

## Core Ideas

- **State comes first**: before defining operations, you identify the state
  variables and the invariants that any valid system state must satisfy.
- **Schemas provide structure**: Z schemas group declarations and constraints,
  making large specifications easier to read, reuse, and refine.
- **Mathematical notation is practical, not decorative**: sets, relations,
  functions, and predicate logic provide a compact language for precise design.
- **Operations are state transformations**: the core question is how an action
  moves the system from one valid state to another, including error cases.

## What This Chapter Covers

- The state-centered philosophy behind Z notation
- Basic mathematical vocabulary, including sets, relations, functions, and
  predicate logic
- State schemas, schema inclusion, and schema design for readability
- Operation schemas with `Δ`, `Ξ`, preconditions, postconditions, and error
  handling
- Schema calculus for composing larger operations from smaller building blocks

## Representative Applications

The Japanese chapter uses examples such as library-style state management and
other structured information systems to show how Z captures valid states,
operation effects, and composition rules. The emphasis is not only on writing
correct formulas, but also on designing specifications that teams can review
and maintain.

## When to Use Z Notation

Z is appropriate when system correctness depends on a clear state model,
rigorous invariants, and carefully specified operations. It is particularly
effective for domains such as resource management, records, workflow state,
control logic, and safety-related data consistency. If concurrency or temporal
evolution is the main concern, Chapters 6 and 7 provide more direct models.

## Relationship to Other Chapters

Chapter 5 builds directly on Chapter 3's discussion of contracts and
invariants. Compared with Alloy in Chapter 4, Z places more emphasis on
state-based abstraction and operation design. The later verification chapters
reuse the same discipline when proving properties or checking models.
