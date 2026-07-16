# Appendix C: Notation Cross-Reference

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
- **refinement**: the process of developing a concrete specification while proving that, after applying a refinement mapping and hiding internal variables, its behavior satisfies the abstract specification. Conceptually, the implication runs as `ConcreteSpec => AbstractSpec`.
- **contract**: a runtime or verification-time guard that makes preconditions and postconditions explicit.
- **trace**: a sequence of state transitions. Counterexamples are presented as traces.
- **counterexample**: a minimal execution that violates a property. It is the starting point for correcting the design.
- **authentication**: a trace property connecting an accepted peer, message, or session to a corresponding legitimate event; state whether the correspondence is non-injective or injective.
- **attack trace**: a violating trace that includes adversary knowledge, message operations, and protocol events.

### C.1.1 Minimal Correspondence for SAT / UNSAT Artifacts

| Outcome | Main retained artifact | What independent rechecking confirms | What it still does not validate |
| --- | --- | --- | --- |
| `SAT` | model / witness | That the assignment satisfies the same encoded constraints | The natural-language requirement, the original specification, or the encoder |
| `UNSAT` | proof certificate | That a checker or kernel accepts the certificate for the input problem | Requirement validity, omitted assumptions, or the full preprocessing chain |
| `unknown` / timeout | logs, resource bounds, input hash | That the run is non-success and needs triage | Correctness or absence of defects |

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

- **Tool-compliant blocks** (`&#12304;Tool-compliant (runs as-is)&#12305;`): notation
  intended to be copied into a tool or CLI and run as-is, although
  project-specific filenames or configuration may still be required
- **Context-dependent snippets** (`&#12304;Context-dependent snippet&#12305;`): real
  tool syntax shown as a fragment; you still need declarations, a model, a
  harness, or surrounding context from the chapter
- **Pseudo-notation blocks** (`&#12304;Pseudo notation&#12305;`): explanatory notation
  that may contain mathematical symbols, omission, or output examples and
  should therefore not be pasted into a tool unchanged

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
| --- | --- | --- | --- | --- |
| Set (type) | `A : ℙ X` | `A: set X` | Event set `{a, b}` / synchronization set `X` | `A ∈ SUBSET X` |
| Membership | `x ∈ A` | `x in A` | Event membership `a ∈ X` | `x ∈ A` |
| Relation | `R : X ↔ Y` | `R: X -> Y` | Usually not written directly | `R ⊆ X × Y` |
| Total function | `f : X → Y` | `f: X -> one Y` | Usually not written directly | `f ∈ [X -> Y]` |
| Partial function | `f : X ⇸ Y` | `f: X -> lone Y` | Usually not written directly | Expressed as a partial function where needed |
| State | State schema | Model time or steps explicitly | Process, with state embedded in transitions | Variable `v` and next-state value `v'` |
| Initial state | `InitState` | `pred Init[...]` | Initial process `P0` | `Init == ...` |
| Transition / operation | `ΔState` | `pred Step[s, s']` | Prefix `a → P` (`a -> P` in tools) | `Next == ...` |
| Invariant (safety) | Schema constraint | `fact` / `assert` | Refinement / assertions, depending on the tool | `Invariant == ...` / `[]P` |
| Liveness / fairness | Requires extension | Expressed over traces | Tool-dependent | `<>P`, `P ~> Q`, `WF_vars(A)`, `SF_vars(A)` |

Notes:
- Z symbols such as `↔`, `→`, `⇸`, and `↦` follow the notation system used in Chapter 5.
- In the prose of this book, CSP uses mathematical symbols such as `→`, `□`, and `⊓`, while tools such as `FDR`/`CSPM` typically use `->`, `[]`, and `|~|`.

### C.3.2 Z Notation: Main Symbols and Reading Guide

| Symbol | Meaning | Example reading |
| --- | --- | --- |
| `ℙ X` | Power set | power set of `X` |
| `x ∈ A` | Membership | `x` is in `A` |
| `R : X ↔ Y` | Relation | relation from `X` to `Y` |
| `f : X → Y` | Total function | total function from `X` to `Y` |
| `f : X ⇸ Y` | Partial function | partial function from `X` to `Y` |
| `x ↦ y` | Maplet, that is, a pair | `x` maps to `y` |
| `dom R`, `ran R` | Domain / range | domain / range |

### C.3.3 Alloy: Main Symbols (Alloy Analyzer 6)

| Symbol | Meaning | Example |
| --- | --- | --- |
| `sig` / field | Sets and relations | `sig User { files: set File }` |
| Multiplicity `one` / `lone` / `some` / `set` | Cardinality constraint | `owner: one User` |
| `fact` | Constraint that always holds | `fact { ... }` |
| `assert` + `check` | Property checking through counterexample search | `check Inv for 5` |
| `run` | Search for satisfying instances | `run { ... } for 5` |
| `.`, `~`, `^` | Join / transpose / transitive closure | `u.files`, `~r`, `^parent` |

### C.3.4 CSP: Main Symbols (Book / Tools)

| Concept | Book notation (mathematical) | Tool notation (representative CSPM/FDR form) |
| --- | --- | --- |
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
| --- | --- | --- |
| `v'` | The next-state value used inside an action; distinct from LTL `X` / `○` | `x' = x + 1` |
| `[]P` / `<>P` | Always / eventually | `[]Inv`, `<>Goal` |
| `P ~> Q` | Whenever `P` holds, `Q` eventually follows | `request ~> response` |
| `WF_vars(A)` / `SF_vars(A)` | Weak / strong fairness assumptions for action `A` | `WF_vars(Receive)` |
| `.cfg` | TLC configuration | initial state, invariants, and exploration constraints |

`WF_vars(A)` and `SF_vars(A)` require declarations for `vars` and action `A`, with `A` defined as a subaction of `Next`, plus a specification context such as `Init /\ [][Next]_vars`; they are not complete runs-as-is examples on their own. A refinement implication is also pseudo-notation until the refinement mapping and hiding boundary are made explicit.

Supplement:
- Alloy is centered on finite-scope counterexample search. When modeling state transitions, time or steps are usually made explicit.
- TLA+ is centered on state transitions and temporal logic. Primes relate current and next states inside actions, while `[]`, `<>`, `~>`, and fairness describe properties of behaviors.
- Z is used to make requirements precise through state and operation schemas and then refine them toward implementation.

### C.3.9 Conceptual Correspondence Between LTL / CTL and Probabilistic Properties

Ordinary LTL and CTL primarily express whether a property holds over paths or a computation tree.
PRISM's PCTL- and CSL-style properties add probability values, thresholds, and expected rewards to related reachability, continuation, and long-run questions.
The table is a reading bridge, not a table of logical equivalences.

| Question | Ordinary LTL / CTL view | Quantitative PRISM view | Additional facts to fix |
| --- | --- | --- | --- |
| Can success be reached? | LTL `F success`; CTL `EF success` / `AF success` | `P=? [ F "success" ]` | Initial state, probability distribution, scheduler scope |
| Does reachability meet a target? | Boolean truth alone does not expose probability mass | `P>=0.99 [ F "success" ]` | Rationale for the threshold, rounding, tolerance |
| What fraction of the long run is operational? | Plain `G` / `AG` means “always,” not a time fraction | `S=? [ "operational" ]` | Steady-state assumptions, initial distribution, absorbing classes |
| What is the cost before completion? | Count events on traces separately | `R{"cost"}=? [ F "done" ]` | Reward units, attachment points, non-reaching paths |
| What bounds include environment choices? | Restrict paths with assumptions such as fairness | MDP `Pmin` / `Pmax`, `Rmin` / `Rmax` | Scheduler/adversary class |
| How is failure explained? | Counterexample trace | Probability value, scheduler, representative paths, critical subsystem | Generation method and coverage |

In particular, do not mechanically identify `P>=1 [ F "success" ]` with `AF success`.
DTMCs, CTMCs, and MDPs assign different meanings to path measures and nondeterminism, and probability one still leaves a boundary around measure-zero paths.
Before comparing formulas, align the model type, initial state, scheduler, fairness assumptions, and time bound.

### C.3.10 Tamarin: Minimal Correspondence for Security-Protocol Verification

Tamarin represents protocol state and adversary knowledge with multiset rewriting rather than a conventional state-variable notation.
This table is only the minimum bridge needed to read the Chapter 13 example.

| Tamarin concept | Reading in this book | Chapter 13 example | Evidence to retain |
| --- | --- | --- | --- |
| Fact | Protocol state, key, message, or adversary knowledge | `!SharedKey`, `OpenChallenge`, `In` / `Out` | Persistent / linear multiplicity, arguments, producing rule |
| Rule | Protocol step that consumes and produces facts | Issue challenge, send response, accept response | Premises, conclusions, action facts |
| Action fact / event | Observation that a lemma references on a trace | `ResponseSent`, `ResponseAccepted` | Participants, session data, ordering |
| Lemma | Trace property for executability, secrecy, or authentication | `Shared_Key_Secrecy`, `Response_Authentication`, `No_Replay` | Quantifiers, assumptions, proof mode, status |
| Attack trace | Concrete execution that falsifies a lemma | Two acceptances of the same ciphertext | Target lemma, steps, adversary message operations |
| Equational theory | Equations that symbolically reduce cryptographic operations | `sdec(senc(m,k),k)=m` | Built-ins, omitted operations, algebraic assumptions |

Distinguish non-injective correspondence such as `Response_Authentication` from an injective property that maps each send to at most one acceptance.
Do not reinterpret symbolic `verified` as an unconditional proof of an implementation or of computational cryptographic security.

### C.3.11 SymbiYosys: Minimal Correspondence for Synchronous RTL Formal Verification

SymbiYosys transforms RTL and properties through Yosys and runs BMC, proof, or reachability tasks with a selected engine and solver.
This table is the minimum bridge needed for the Chapter 8 arbiter example, not a syntax reference for all of SystemVerilog Assertions.

| RTL / formal concept | Chapter 8 expression | Checking meaning | Evidence to retain |
| --- | --- | --- | --- |
| Clock edge | `always_ff @(posedge clk)` | One step of the register transition system | Clock, mode, depth |
| Reset contract | `assume` `rst` only at the first edge | Restrict the environment to the intended initialization sequence | Reset polarity, asserted duration, assumption |
| Safety property | `assert(!(grant0 && grant1))` | Forbid simultaneous grants | Property location, PASS / FAIL |
| Environment constraint | `assume(...)` | Restrict input traces enumerated by the solver | Every assumption and its rationale |
| Reachability target | `cover(...)` | Find one execution that reaches an interesting state | Reach step, witness VCD |
| BMC | `mode bmc`, `depth 6` | Search for assertion violations within six steps | Bound, counterexample VCD |
| k-induction | `mode prove`, `depth 6` | Check the base case and temporal induction | Status of both phases, engine |
| Sampled prior value | `$past(req0)` | Request value at the preceding clock edge | Guard for the first sample |

An `assert` can pass vacuously when an over-strong `assume` removes the defective trace.
Use `cover` to confirm important environment conditions such as simultaneous requests, and do not treat an unreachable cover as a safety success.

### C.3.12 RTLola: Minimal Correspondence for Runtime Verification

Runtime verification checks an event trace obtained through instrumentation against a property; it does not explore every behavior of a design model.
This table is the minimum bridge needed for the Chapter 11 authentication example, not a full RTLola or stream-processing syntax reference.

| Runtime-verification concept | Chapter 11 expression | Checking meaning | Evidence to retain |
| --- | --- | --- | --- |
| Input event field | `auth_success`, `sensitive_operation`, `time` | Observation passed from a CSV row to the monitor | Schema, unit, type, missing-data policy |
| Derived state / output stream | `authenticated` | Monitor state remembering a prior successful authentication | Initial value, update expression, session boundary |
| Previous value | `offset(by: -1).defaults(to: false)` | Previous event's monitor state and its initial default | Offset semantics, trace start |
| Trigger | Sensitive operation before authentication | Verdict for a safety-property violation | Timestamp, message, property ID |
| Finite trace | Three-row relative-time CSV | Check only the observed finite prefix | First/last time, row count, input hash |
| Online / offline | This example uses `--offline relative-float-secs` | Deterministically replay a retained trace | Mode, clock, ordering, tool version |
| No violation | Zero findings for the normal trace | No target violation was detected in that prefix | Explicit non-claim about unobserved runs |
| Expected violation | One finding for the violating trace | The monitor detects a known violation | Comparison with an independently derived expected result |

Do not move infinite-trace LTL operators such as `G` or `F` onto a finite log without defining the end-of-trace `true` / `false` / inconclusive result, deadlines, and missing-data handling.
If an event is never collected, the monitor cannot infer that fact automatically, so evaluate observability and monitorability separately from the property itself.
