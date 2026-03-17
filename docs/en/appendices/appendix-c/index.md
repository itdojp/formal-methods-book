---
layout: book
title: "Appendix C: Notation Cross-Reference"
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-c.md"
---
# Appendix C: Notation Cross-Reference

> Translation status: full draft  
> Japanese source of truth: `src/ja/appendices/appendix-c.md`

This appendix collects the minimum set of frequently used terms and symbols in formal methods together with the Definition of Done checklist for the AI era.

## C.1 Glossary

- **invariant**: a property that must always hold. If a counterexample appears, it indicates a breakdown in the specification or the implementation.
- **safety**: a property stating that something bad does not happen, for example that a double withdrawal never occurs.
- **liveness**: a property stating that something good eventually happens, for example that a request is eventually processed.
- **refinement**: the process of making an abstract specification progressively more concrete until it reaches an implementation-level specification.
- **contract**: a runtime or verification-time guard that makes preconditions and postconditions explicit.
- **trace**: a sequence of state transitions. Counterexamples are presented as traces.
- **counterexample**: a minimal execution that violates a property. It is the starting point for correcting the design.

## C.2 Definition of Done Checklist for the AI Era

In AI-assisted development, the premise is that the correctness of outputs is backed by verifiers.

- If there is a change in the specification, the corresponding formal specification has also been updated
- Verification logs include the seed, depth, scope, and execution command
- If a counterexample appears, the fix history and re-verification logs remain available
- The reason for any exception approval, the fallback measure, and the follow-up deadline are stated explicitly

## C.3 Notation Cross-Reference (Z / Alloy / CSP / TLA+)

The following table gives a minimum correspondence for how the same concept is expressed in each notation. Entries are limited to what is consistent with the chapter-level notation used in this book, especially Chapter 4 on Alloy, Chapter 5 on Z, Chapter 6 on CSP, and Chapter 7 on TLA+.

Code-block labels:
- **`【ツール準拠（そのまま動く）】`**: notation intended to be copied directly into a tool or CLI and executed as-is, although extra configuration may still be required depending on the environment.
- **`【文脈依存スニペット】`**: syntax that follows a real tool, but is only a fragment and therefore requires declarations, a model, a harness, or an interactive context elsewhere.
- **`【擬似記法】`**: notation used for explanation that may contain mathematical notation, omitted detail, or output examples and therefore is not guaranteed to be strict tool input.

Notes:
- Inside a code fence labeled **`【ツール準拠（そのまま動く）】`**, include only strings that are valid as tool input. Do not mix in output examples, diagrams, or natural-language explanation.
- If mandatory surrounding elements such as variable declarations, `MODULE main`, a verification harness, or an interactive context are defined elsewhere, use **`【文脈依存スニペット】`**.
- If the surrounding mandatory elements are explicitly identified in the text or a referenced location, the fragment is treated as **`【文脈依存スニペット】`**. If references are not identified or the fragment includes mathematical notation, omission, or natural language, it is treated as **`【擬似記法】`**.
- Diagrams, output examples, and pseudocode should use **`【擬似記法】`**.

### C.3.1 Concept Correspondence (Minimum Set)

| Concept | Z notation (in this book) | Alloy (assuming Alloy Analyzer 6) | CSP (in this book / tools) | TLA+ (assuming TLC) |
|---|---|---|---|---|
| Set (type) | `A : ℙ X` | `A: set X` | Event set `{a, b}` / synchronization set `X` | `A ∈ SUBSET X` |
| Membership | `x ∈ A` | `x in A` | Event membership `a ∈ X` | `x ∈ A` |
| Relation | `R : X ↔ Y` | `R: X -> Y` | Usually not written directly | `R ⊆ X × Y` |
| Total function | `f : X → Y` | `f: X -> one Y` | Usually not written directly | `f ∈ [X -> Y]` |
| Partial function | `f : X ⇸ Y` | `f: X -> lone Y` | Usually not written directly | Expressed as a partial function where needed |
| State | State schema | Model time or steps explicitly | Process, with state embedded in transitions | Variable `v` and next-state value `v'` |
| Initial state | `InitState` | `pred Init[...]` | Initial process `P0` | `Init == ...` |
| Transition / operation | `ΔState` | `pred Step[s, s']` | Prefix `a → P` (`a -> P` in tools) | `Next == ...` |
| Invariant (safety) | Schema constraint | `fact` / `assert` | Refinement / assertions, depending on the tool | `Invariant == ...` / `[]P` |
| Liveness / fairness | Requires extension | Expressed over traces | Tool-dependent | `<>P`, `WF_vars(A)`, `SF_vars(A)` |

Notes:
- Z symbols such as `↔`, `→`, `⇸`, and `↦` follow the notation system used in Chapter 5.
- In the prose of this book, CSP uses mathematical symbols such as `→`, `□`, and `⊓`, while tools such as `FDR`/`CSPM` typically use `->`, `[]`, and `|~|`.

### C.3.2 Z Notation: Main Symbols and Reading Guide

| Symbol | Meaning | Example reading |
|---|---|---|
| `ℙ X` | Power set | power set of `X` |
| `x ∈ A` | Membership | `x` is in `A` |
| `R : X ↔ Y` | Relation | relation from `X` to `Y` |
| `f : X → Y` | Total function | total function from `X` to `Y` |
| `f : X ⇸ Y` | Partial function | partial function from `X` to `Y` |
| `x ↦ y` | Maplet, that is, a pair | `x` maps to `y` |
| `dom R`, `ran R` | Domain / range | domain / range |

### C.3.3 Alloy: Main Symbols (Alloy Analyzer 6)

| Symbol | Meaning | Example |
|---|---|---|
| `sig` / field | Sets and relations | `sig User { files: set File }` |
| Multiplicity `one` / `lone` / `some` / `set` | Cardinality constraint | `owner: one User` |
| `fact` | Constraint that always holds | `fact { ... }` |
| `assert` + `check` | Property checking through counterexample search | `check Inv for 5` |
| `run` | Search for satisfying instances | `run { ... } for 5` |
| `.`, `~`, `^` | Join / transpose / transitive closure | `u.files`, `~r`, `^parent` |

### C.3.4 CSP: Main Symbols (Book / Tools)

| Concept | Book notation (mathematical) | Tool notation (representative CSPM/FDR form) |
|---|---|---|
| Prefix | `a → P` | `a -> P` |
| External choice | `P □ Q` | `P [] Q` |
| Internal choice | `P ⊓ Q` | <code>P &#124;~&#124; Q</code> |
| Synchronous parallel with synchronization set `X` | <code>P [&#124; X &#124;] Q</code> | <code>P [&#124; X &#124;] Q</code> |
| Interleaving | <code>P &#124;&#124;&#124; Q</code> | <code>P &#124;&#124;&#124; Q</code> |
| Hiding | `P \ X` | `P \\ X` |
| Renaming | `P[[ a ← b ]]` | `P[[ a <- b ]]` |

Note: the tool notation shown here is representative only. In actual work, confirm the details against the specific tool and CSP dialect in use.

### C.3.5 TLA+: Main Symbols (TLC)

| Symbol | Meaning | Example |
|---|---|---|
| `v'` | The next-state value | `x' = x + 1` |
| `[]P` / `<>P` | Always / eventually | `[]Inv`, `<>Goal` |
| `WF_vars(A)` / `SF_vars(A)` | Fairness assumptions | `WF_vars(Next)` |
| `.cfg` | TLC configuration | initial state, invariants, and exploration constraints |

Supplement:
- Alloy is centered on finite-scope counterexample search. When modeling state transitions, time or steps are usually made explicit.
- TLA+ is centered on state transitions and temporal logic. It is typically used to fix high-level properties such as invariants and liveness before implementation detail is fully developed.
- Z is used to make requirements precise through state and operation schemas and then refine them toward implementation.
