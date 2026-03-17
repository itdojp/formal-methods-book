# Appendix C: Notation Cross-Reference

> Translation status: full draft  
> Japanese source of truth: `src/ja/appendices/appendix-c.md`

This appendix is a quick lookup guide for readers who need to recover the
meaning of a term, compare notations across methods, or check what disciplined
AI-assisted verification work should leave behind. For fuller definitions, use
the main [Glossary]({{ '/en/glossary/' | relative_url }}). Use this appendix
when you need a compact reference rather than a full chapter-length
explanation.

## C.1 Quick Reference Terms

- **invariant**: a property that must always hold. If a counterexample appears, it indicates a breakdown in the specification or the implementation.
- **safety**: a property stating that something bad does not happen, for example that a double withdrawal never occurs.
- **liveness**: a property stating that something good eventually happens, for example that a request is eventually processed.
- **refinement**: the process of making an abstract specification progressively more concrete until it reaches an implementation-level specification.
- **contract**: a runtime or verification-time guard that makes preconditions and postconditions explicit.
- **trace**: a sequence of state transitions. Counterexamples are presented as traces.
- **counterexample**: a minimal execution that violates a property. It is the starting point for correcting the design.

## C.2 Definition of Done Checklist for AI-Assisted Work

In AI-assisted development, the key question is not whether AI was used, but
whether the resulting claims are backed by verifiable evidence.

- If there is a change in the specification, the corresponding formal specification has also been updated
- Verification logs include the seed, depth, scope, and execution command
- If a counterexample appears, the fix history and re-verification logs remain available
- The reason for any exception approval, the fallback measure, and the follow-up deadline are stated explicitly

## C.3 Notation Cross-Reference (Z / Alloy / CSP / TLA+)

The tables below give a minimum correspondence for how the same concept is
expressed in each notation. They are intentionally compact and are limited to
the notation used in this book, especially Chapter 4 on Alloy, Chapter 5 on Z,
Chapter 6 on CSP, and Chapter 7 on TLA+.

When reading chapter examples, three block labels matter:

- **Tool-compliant blocks**: notation intended to be copied into a tool or CLI
  and run as-is, although project-specific filenames or configuration may still
  be required
- **Context-dependent snippets**: real tool syntax shown as a fragment; you
  still need declarations, a model, a harness, or surrounding context from the
  chapter
- **Pseudo-notation blocks**: explanatory notation that may contain
  mathematical symbols, omission, or output examples and should therefore not
  be pasted into a tool unchanged

Notes:
- Inside a tool-compliant block, include only strings that are valid as tool
  input. Do not mix in output examples, diagrams, or natural-language
  explanation.
- If mandatory surrounding elements such as variable declarations,
  `MODULE main`, a verification harness, or an interactive context are defined
  elsewhere, the example should be treated as a context-dependent snippet.
- Diagrams, output examples, and pseudocode should be treated as
  pseudo-notation.

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
