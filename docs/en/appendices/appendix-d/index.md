---
layout: book
title: "Appendix D: Exercise Guides and Self-Review Frameworks"
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-d.md"
---
# Appendix D: Exercise Guides and Self-Review Frameworks

This appendix provides reusable answer frameworks for the end-of-chapter exercises. Use it when you want to turn an exercise into a study note, workshop output, or review packet that another reader can inspect.
Because end-of-chapter exercises do not usually have a single unique answer, this appendix emphasizes the **solution skeleton** (minimum structure), the evidence worth keeping, and the **self-review criteria** you can apply before treating an answer as complete.

Notes:
- The pseudo-scripts, log structures, and configuration examples in this appendix are illustrative. In actual practice, adjust them to the project environment and requirements.
- Numerical values such as percentages, multipliers, and counts should either cite a source or explicitly state that they are illustrative.

## D.1 Common Output Structures and Self-Review Criteria

### Common Work Products (Recommended)

- Problem setting: target, assumptions, and boundaries (`in-scope` / `out-of-scope`)
- Specification: term definitions, preconditions, and properties such as safety, liveness, and contracts
- Verification: execution commands, settings such as seed, depth, scope, and time limit, and result logs
- Counterexample handling, when a counterexample appears: minimal trace, hypotheses about the cause, fix diff, and re-verification logs (see Appendix F)

### Common Self-Review Criteria

- Accuracy: definitions, constraints, and reasoning are consistent
- Completeness: no required viewpoint is omitted, including exceptions and boundary conditions
- Consistency: terminology, symbols, and abstraction level are aligned
- Reproducibility: a third party can rerun the same process by using the same commands, settings, and logs
- Validity: assumptions such as environment model, failure model, and performance constraints are stated explicitly

## D.2 Chapter 1

### Thought Exercise 1: Complexity Analysis

Hints (steps):
1. Fix the system boundary, including external APIs, dependencies, and operations.
2. Enumerate components and interactions, and organize them from the viewpoint of combinatorial explosion, such as the number of states and transitions.
3. Identify failure modes such as partial failure, races, and specification mismatches, and provisionally define a required assurance level comparable to `SIL`.

Model answer (outline):
- A component list with roles and responsibilities, plus an interaction diagram
- An evaluation of how states and transitions grow, including which part explodes combinatorially
- Failure modes and safety requirements, together with the basis for the `SIL`-level judgment

Self-review criteria:
- The system boundary is clear, with few missing assumptions
- Complexity is explained in terms of both interaction and state space
- Failure modes are concrete and include operational aspects

### Practical Exercise: Accident Analysis and Preventive Measures

Hints (steps):
1. Decompose the direct causes and root causes of the accident into specification, implementation, operation, and organization.
2. State which property was violated, such as an invariant, a contract, safety, or liveness.
3. Organize which abstraction level should be addressed first and whether `Alloy`, `TLA+`, or program verification is the most suitable approach.

Model answer (outline):
- A cause analysis covering both technical and organizational factors, plus the contribution of specification ambiguity
- A map of what could have been prevented, connected to the methods in Chapters 4, 8, and 10
- Similar modern risks and practical preventive actions in business settings

Self-review criteria:
- The factors of the accident are decomposed appropriately
- The discussion is reduced to properties that can actually be verified
- The proposal is concrete, including introduction steps, verification gates, and exception flows

### Practical Exercise: Quantitative Analysis of Specification Ambiguity

Hints (steps):
1. Enumerate ambiguous words and separate the branching points in interpretation, such as limits on the number of attempts, the definition of failure, or the granularity of error messages.
2. Estimate implementation variants as a product of branching factors. The estimate does not have to be exact, but it should be explainable.
3. Evaluate security risks on three axes: attack surface, observability, and operational impact.

Model answer (outline):
- A table of ambiguities with columns such as ambiguous point, interpretation candidates, branch count, and impact
- A rough estimate of the total number of implementation patterns and the basis for that calculation
- A prioritization of what should be fixed first through specification work, as discussed in Chapter 3

Self-review criteria:
- Ambiguities are extracted sufficiently
- The basis of the estimate is explicit
- Security considerations are included

### Advanced Exercise: Planning Business Adoption

Hints (steps):
1. Choose candidate application areas where failure cost is high, specifications are ambiguous, or concurrency and distribution are present.
2. Select a set of roughly three chapters to study in the order that can be reproduced most directly in your own work.
3. Build consensus by presenting ROI, as discussed in Chapter 11, and a staged rollout across pull requests, nightly runs, and pre-release runs.

Model answer (outline):
- A list of candidate application areas with scope, expected effect, and risk
- A six-month to one-year learning and practice plan with deliverables and KPIs
- An organizational proposal covering return on investment, guardrails, and exception flow

Self-review criteria:
- Target selection is rational
- Deliverables and KPIs are concrete
- The explanation to the organization is realistic

## D.3 Chapter 2

### Reading Check Exercise 1: Set-Theoretic Representation of Data Structures

Hints (steps):
1. Define the type of `Student` as a Cartesian product such as `Name × Age × Courses`.
2. Make clear whether `Courses` is treated as a set, a sequence, or a multiset.
3. Define the relation “is enrolled in” as `Student ↔ Course`.

Model answer (outline):
- `Student == Name × Nat × P(Course)` as an example when `Courses` is treated as a set
- `students ⊆ Student` as an example when students are treated as a set; if order matters, use a sequence instead
- `enrolled ⊆ Student × Course` and a membership test such as `⟨s,c⟩ ∈ enrolled`

Self-review criteria:
- The type choice is consistent
- Relations and functions are used appropriately
- Boundaries such as ordering and duplication are stated explicitly

### Reading Check Exercise 2: Logic and Control Structure

Hints (steps):
1. Decompose natural-language conditions into propositions such as `P`, `Q`, and so on, and translate them into logical formulas.
2. For quantification such as `∀` and `∃`, make the set boundary explicit, for example the set of users or products.
3. In implementation-level conditions, also state assumptions about `null`, unset values, and exceptions.

Model answer (outline):
- Example: `canDrive ⇔ (age>=18) ∧ hasValidLicense`
- Example: `canDelete ⇔ isAdmin ∨ isOwner`
- Example: `∀u ∈ Users : hasValidEmail(u)`
- Example: `∃p ∈ Products : inStock(p)`

Self-review criteria:
- The logical formulas capture the requirements without excess or omission
- Quantification ranges are explicit
- Exceptions are considered when mapping the logic to implementation

### Practical Exercise: State Modeling

Hints (steps):
1. Define the minimum set of state variables, such as inserted amount, selection, inventory, and change.
2. Define transitions for each input event, such as insertion, selection, and cancellation.
3. Build invariants around money conservation, non-negative stock, and absence of invalid transitions.

Model answer (outline):
- State variables such as `balance`, `stock`, `selected`, and `change`
- Input set such as `Insert100`, `Insert500`, `SelectCola`, `SelectTea`, and `Cancel`
- Example invariants such as `balance>=0`, `stock[item]>=0`, and `purchase => balance>=price`

Self-review criteria:
- The state space and inputs are covered comprehensively
- Invariants correspond to the requirements
- Scenarios are consistent as transition sequences

### Advanced Exercise: Concurrency Analysis

Hints (steps):
1. Decompose a transaction into `read → compute → write` and model those as transitions.
2. Enumerate interleavings and observe whether key properties such as non-negative balance and conservation are preserved.
3. Choose candidate constraints from exclusivity, atomic operations, retry, and ordering.

Model answer (outline):
- An example showing how an interleaving causes a lost update
- An inconsistency condition, for example that the final balance differs from the result of sequential execution
- Candidate constraints such as locking, transactions, or `CAS`

Self-review criteria:
- Interleavings are enumerated correctly
- The conditions under which inconsistency occurs are explained
- The constraints are reasonable, including their side effects

### Integrated Exercise: Preparation for Formal Methods

Hints (steps):
1. First fix sets, relations, and invariants in natural language and then map them to the selected methods.
2. Use the role allocation in Figure 2-2 to decide which of `Alloy`, `Z`, `CSP`, and `TLA+` is best suited to each problem.

Model answer (outline):
- Exercise 1 (`Alloy`): assign entities, relations, and constraints such as “there is at least one administrator” to `sig`, `fact`, and `assert`
- Exercise 2 (`Z`): define state schemas and operation schemas, including both normal and error cases, and separate preconditions from postconditions
- Exercise 3 (`CSP`): define processes, channels, and order constraints, and enumerate deadlock-related viewpoints
- Exercise 4 (`TLA+`): describe state variables, safety, liveness, and fairness assumptions separately

Self-review criteria:
- The method assignment is rational
- Invariants, liveness, and exception handling are covered
- The connection to the following chapters is clear, including what will actually be created next

## D.4 Chapter 3

### Basic Understanding Exercise 1: Identifying Ambiguity

Hints (steps):
1. Enumerate words whose threshold or judging party is unclear, such as “appropriately,” “too large,” or “invalid.”
2. Organize the effect of each interpretation on design and operations, including logs, audit, and retry handling.

Model answer (outline):
- A table from ambiguous term to interpretation candidates to impact, such as false positives, false negatives, UX, and operational burden
- A prioritization of the items that should be fixed first through specification work

Self-review criteria:
- Ambiguity is extracted sufficiently
- The impact analysis includes implementation and operational effects

### Basic Understanding Exercise 2: Writing Contracts

Hints (steps):
1. Preconditions describe when the input is searchable, for example sortedness and value range.
2. Postconditions describe the property of the return value in both found and not-found cases.
3. Frame conditions should explicitly state what is not changed, such as the array itself.

Model answer (outline):
- Precondition: `sorted(sorted_array)`, `sorted_array != null`
- Postcondition (found): `0<=ret<n ∧ sorted_array[ret]=target`
- Postcondition (not found): `ret=-1 ∧ ∀i. sorted_array[i] != target`
- Frame condition: `sorted_array` is not modified

Self-review criteria:
- Preconditions, postconditions, and frame conditions are separated
- The return-value conditions are complete for both cases

### Practical Exercise 1: Specifying a Queue

Hints (steps):
1. Represent the state as a sequence so that FIFO is easy to express.
2. For each operation, define the relationship between the updated state and the return value.
3. Handle errors such as dequeue from an empty queue either as preconditions or as exception cases.

Model answer (outline):
- State: `Q` as a sequence
- `enqueue`: `Q' = Append(Q, x)`
- `dequeue` on a non-empty queue: `ret = Head(Q) ∧ Q' = Tail(Q)`
- Definitions of `isEmpty`, `size`, and `front`
- Invariants such as `size(Q) >= 0` and, where needed, element-type constraints

Self-review criteria:
- FIFO is reflected in the specification
- Preconditions and exceptions are clear
- The operations are mutually consistent, for example `front` and `dequeue`

### Practical Exercise 2: Invariants for an Email System

Hints (steps):
1. Define data integrity first, including referential consistency and duplicate elimination.
2. Separate security requirements such as credentials and access control as invariants.
3. Add business rules such as message ownership and movement into trash.

Model answer (outline):
- Integrity examples: email addresses are unique; senders and recipients belong to the user set
- Security examples: plain-text passwords are prohibited, with hashing assumed; operations require login
- Rule examples: each message belongs to one of inbox, sent, or trash; duplicate message IDs are prohibited

Self-review criteria:
- Invariants are categorized clearly
- Referential relationships cannot break
- Exceptions such as deletion, movement, and undelivered mail are considered

### Advanced Exercise: Validating a Specification

Hints (steps):
1. Check consistency by composing operations such as `enqueue → dequeue` and confirming that no contradiction appears.
2. Check completeness by listing use patterns such as empty, full, and boundary cases.
3. Map the specification to a test strategy through boundaries, equivalence classes, and counterexamples.

Model answer (outline):
- A checklist of viewpoints for reviewing the specification
- Notes on implementability, such as time complexity and data structures
- A skeleton for test-case design

Self-review criteria:
- Verification viewpoints are systematized
- The route from specification to testing is explicit

## D.5 Chapter 4

### Basic Exercise 1: Reading an Alloy Model

Hints (steps):
1. State in words what multiplicities such as `lone`, `set`, and `one` mean.
2. Separate the roles of `fact`, which is a constraint that always holds, and `assert`, which is an explicit check target for counterexample search.
3. Consider missing constraints such as prohibition of self-marriage or cyclic parent-child relations.

Model answer (outline):
- `spouse: lone Person` means “at most one spouse”
- Bidirectional consistency between `parents` and `children`
- Possible missing constraints: `p.spouse != p`, acyclicity of parent-child relations, and mutual exclusiveness of spouses, such as no bigamy

Self-review criteria:
- The meaning of each constraint can be explained
- Validity can be discussed in relation to the business requirement

### Basic Exercise 2: Writing Constraints

Hints (steps):
1. Separate `User`, `Book`, and `Loan`, and represent lending either as a relation or as a `Loan` entity.
2. Fix rules such as “at most five books” and “no overdue borrowing” as `fact`s.
3. You may abstract the return date, for example by replacing explicit date ordering with an overdue flag.

Model answer (outline):
- `sig User { loans: set Loan }`, `sig Book {}` and similar declarations
- `fact UniqueLoan { all b: Book | lone l: Loan | l.book = b }`
- `fact Limit { all u: User | #u.loans <= 5 }`
- `fact Overdue { all u: User | u.overdue => no u.newLoan }` as an example

Self-review criteria:
- Requirements are turned into constraints without excess or omission
- The assumptions of the abstraction are stated explicitly

### Practical Exercise 1: Modeling a Security Policy

Hints (steps):
1. Isolate access decisions as predicates such as `canRead` and `canWrite`.
2. Use `fact` for invariants and `assert` for properties that must never be violated.
3. State administrator privileges explicitly as exceptions, including their priority.

Model answer (outline):
- `sig User { groups: set Group }`, `sig File { owner: one User, mode: one Mode, sharedWith: set Group }`
- `pred canWrite[u,f] { u=f.owner or u in Admins and f.mode=RW ... }`
- `assert NoWriteToRO { all u,f | f.mode=RO implies not canWrite[u,f] }`

Self-review criteria:
- The permission model is free from contradiction
- The assertions correspond to the requirements

### Practical Exercise 2: Model Checking and Improvement

Hints (steps):
1. Use `run` to generate instances and identify both realistic and unrealistic cases.
2. Use `check` and scope changes to obtain counterexamples, starting with small scopes.
3. Apply fixes in the order of missing or excessive constraints, and then rerun verification and regression checks by adding assertions where needed.

Model answer (outline):
- A minimal counterexample log and an explanation of what was violated
- A history from hypothesis about the cause, to constraint fix, to re-verification

Self-review criteria:
- Counterexamples are handled as facts and separated from speculation
- The fix is minimal and includes regression prevention

### Advanced Exercise: Modeling Dynamic Behavior

Hints (steps):
1. Represent time or steps with something like `sig Time`, and carry state as a relation such as `balance: Time -> Account -> Int`.
2. Write operations in a form such as `pred Withdraw[t,t']` and state conservation as an invariant.

Model answer (outline):
- Definitions of state variables such as balance and history, together with operations such as deposit and withdrawal
- Invariants such as non-negative balance, total-amount conservation within the model boundary, and history consistency

Self-review criteria:
- State and operations are connected through time
- Invariants are defined in a form that can actually be checked

## D.6 Chapter 5

### Basic Understanding Exercise 1: Reading and Analyzing Schemas

Hints (steps):
1. Read the types such as sets, relations, and partial functions, and explain the meaning of `dom` and `ran` constraints.
2. Decompose each constraint into referential consistency and existence guarantees.

Model answer (outline):
- The types and meanings of variables such as `students`, `courses`, and `enrollment`
- Explanations of consistency constraints such as `dom enrollment ⊆ students`
- Identification of requirements that are not yet represented, such as maximum enrollment count or how to handle missing grades

Self-review criteria:
- `dom` and `ran` are interpreted correctly
- You can explain what each constraint prevents

### Basic Understanding Exercise 2: Creating Operation Schemas

Hints (steps):
1. For the normal case, separate `Δ State` and the preconditions and postconditions.
2. For error cases, use state-preserving schemas such as `Ξ State` and express the reason for the error through output.

Model answer (outline):
- Normal case: existence check plus no-duplicate check, then update `enrollment`
- Error cases: separate schemas for student not found, course not found, and duplicate enrollment
- Integration: define the overall behavior as a schema union of the normal and error cases

Self-review criteria:
- Normal and error cases are separated
- The effect of state updates can be tracked clearly

### Practical Exercise 1: Modeling a Banking System

Hints (steps):
1. Represent customers, accounts, and transactions as sets and relations, and use invariants to express uniqueness and referential consistency.
2. Make transfer composable as withdrawal plus deposit.

Model answer (outline):
- State such as `accounts`, `owners`, `balance`, and `txs`
- Invariants such as non-negative balances, unique account numbers, existing owners, and transaction referential consistency
- Operations such as open, deposit, withdraw, and transfer, with preconditions, postconditions, and error handling

Self-review criteria:
- The invariants correspond to the intended constraints
- The operations preserve the invariants

### Practical Exercise 2: Using Schema Operations

Hints (steps):
1. Define authentication as a common schema and compose it with each operation.
2. For integrating normal and error cases, unify the result type, for example as success or failure.
3. Express atomicity in the specification by stating that the state rolls back when an intermediate failure occurs.

Model answer (outline):
- Create `Auth` and `Log` schemas and compose them with the operation schemas
- Unify errors through an `ErrorCode`
- Compose transfer and guarantee `Ξ State` on failure

Self-review criteria:
- Schema operations are used in a reasonable place
- The state under exceptions is defined clearly

### Advanced Exercise: Specifying a Real-Time System

Hints (steps):
1. Make time and timers explicit as state variables.
2. Fix safety properties such as “simultaneous green is forbidden” as invariants, and define liveness and fairness separately.

Model answer (outline):
- State schemas for signal state, sensors, pedestrian requests, and timers
- Operation schemas for transitions such as signal changes
- Properties such as safety, liveness, and fairness listed in a verifiable form

Self-review criteria:
- Safety is expressed as an invariant
- Time constraints are reflected in the specification

## D.7 Chapter 6

### Basic Understanding Exercise 1: Reading CSP Notation

Hints (steps):
1. Explain the meaning of process, channel, and composition such as parallelism and choice.
2. Trace the behavior under the assumption of synchronized send/receive handshakes.

Model answer (outline):
- A step-by-step interpretation of the process definitions
- Synchronization points in the composition, together with examples of possible traces

Self-review criteria:
- The notation is explained correctly
- The explanation can be grounded in concrete traces

### Basic Understanding Exercise 2: Deadlock Analysis

Hints (steps):
1. Identify mutual waiting caused by both sides waiting to receive or both sides waiting to send.
2. Candidate avoidance strategies include agreeing on order, introducing asynchrony, and timeouts, but also explain their side effects.

Model answer (outline):
- A minimal deadlock example with two processes and reverse send/receive order
- Avoidance strategies and their side effects, such as order inversion, infinite buffers, or added delay

Self-review criteria:
- The deadlock state can be explained
- The avoidance strategy is realistic and includes side effects

### Practical Exercise 1: Designing an ATM System

Hints (steps):
1. Separate `ATM`, `BankServer`, and `User` as processes and connect them through channels.
2. Organize safety properties such as non-negative balances and no double withdrawal separately from liveness such as eventual response.

Model answer (outline):
- A decomposition into processes and the main channels
- Handling of failure cases such as timeout, retry, and interruption

Self-review criteria:
- The protocol order constraints are clear
- Failure cases are considered

### Practical Exercise 2: Using Process Composition

Hints (steps):
1. Be careful not to allow too much behavior in the specification when composing processes.
2. Check properties after composition, such as absence of deadlock and reachability.

Model answer (outline):
- The composition procedure and the properties that should hold afterward
- A summary of the verification results

Self-review criteria:
- The purpose of the composition can be explained
- Side effects introduced by composition are understood

### Advanced Exercise: Designing a Distributed System

Hints (steps):
1. State assumptions about asynchronous communication, delay, and loss explicitly.
2. Include failure detection, retransmission, and idempotence in the design.

Model answer (outline):
- A failure model and the protocol skeleton
- Definitions of safety and liveness properties

Self-review criteria:
- The failure model is stated explicitly
- The design is connected to the intended properties

## D.8 Chapter 7

### Basic Understanding Exercise 1: Understanding Temporal Logic Notation

Hints (steps):
1. Map `[]` (“always”) and `<>` (“eventually”) to the corresponding requirement sentences.
2. Separate fairness assumptions such as `WF` and `SF` as assumptions for “eventually makes progress.”

Model answer (outline):
- Convert each property into forms such as `[]P`, `<>Q`, and `P => <>Q`
- Candidate fairness assumptions

Self-review criteria:
- Safety and liveness are not confused
- Fairness is made explicit as an assumption

### Basic Understanding Exercise 2: Writing State and Actions

Hints (steps):
1. Write variables, which represent state, separately from actions, which represent transitions.
2. Define `Init` and `Next`, and summarize them as `Spec == Init /\ [][Next]_vars`.

Model answer (outline):
- Definitions of the state variables
- Skeletons for `Init`, `Next`, and `Invariant`

Self-review criteria:
- The description follows the basic TLA+ structure
- Variable updates are consistent

### Practical Exercise 1: Designing a Mutual Exclusion Protocol

Hints (steps):
1. Define the critical section and the mutual exclusion invariant `~(crit[0] /\ crit[1])`.
2. If liveness is included, review whether the fairness assumptions are too weak or too strong.

Model answer (outline):
- State such as `flag`, `turn`, and the definition of `Next`
- The invariant for mutual exclusion and, if needed, a liveness property expressing eventual entry

Self-review criteria:
- The invariant is not violated
- Fairness is handled reasonably

### Practical Exercise 2: Producer-Consumer Problem

Hints (steps):
1. Make the assumptions about the buffer, whether bounded or unbounded, and about backpressure explicit.
2. Separate safety such as no out-of-bounds access or overflow from liveness such as continued progress.

Model answer (outline):
- Buffer state and operations such as `produce` and `consume`
- Invariants such as `0 <= count <= N`

Self-review criteria:
- Safety and liveness are separated clearly
- The assumption of boundedness is stated explicitly

### Advanced Exercise: Designing a Distributed System

Hints (steps):
1. State assumptions about message delay, loss, and duplication.
2. Design retransmission, acknowledgments, timeout stopping conditions, and idempotence.

Model answer (outline):
- A failure model and protocol
- Definitions of safety, such as no duplicate processing, and liveness, such as eventual delivery

Self-review criteria:
- Assumptions and properties are consistent
- The retransmission strategy includes stopping conditions

## D.9 Chapter 8

### Basic Understanding Exercise 1: Practicing Temporal Logic

Hints (steps):
1. Reduce states and events to propositions and map them into LTL or CTL syntax.
2. Describe fairness and efficiency by separating assumptions from properties.

Model answer (outline):
- Safety: `AG(door_open -> AX ~moving)` as a CTL example, or `[](door_open => ~moving)` as an LTL example
- Liveness: `AG(call -> AF arrive)` as a CTL example, or `[](call => <>arrive)` as an LTL example

Self-review criteria:
- CTL and LTL are used appropriately
- The propositionalization of states and events is consistent

### Basic Understanding Exercise 2: State-Space Analysis

Hints (steps):
1. Estimate the number of states by multiplying counter values by the local states of each process.
2. Races occur when read-modify-write is split.

Model answer (outline):
- A rough count of the number of states, such as values `0-10` times local states
- A race example such as lost update
- Conditions under which partial-order reduction is effective, namely when independent transitions can be swapped

Self-review criteria:
- The method for counting states can be explained
- The cause of the race is concrete

### Practical Exercise 1: Verification with SPIN

Hints (steps):
1. Define processes such as reader and writer and the shared resource in `Promela`.
2. Express safety properties such as no simultaneous writes with `assert` or LTL.
3. During verification, preserve the seed, exploration limit, and counterexamples.

Model answer (outline):
- The model in `Promela` and the properties as `assert` or LTL
- A summary of the execution log and the counterexample if one appears

Self-review criteria:
- The properties correspond to the requirements
- Counterexamples are reproducible

### Practical Exercise 2: Verification with NuSMV

Hints (steps):
1. Define state variables such as the signal state, sensors, and requests.
2. Write safety properties as invariants in CTL or LTL, such as the prohibition of simultaneous green.

Model answer (outline):
- A `NuSMV` model and the associated properties
- A summary of the verification result, including the trace if a counterexample appears

Self-review criteria:
- Safety, liveness, and responsiveness are separated
- Interpretation of the counterexample is reasonable

### Advanced Exercise: Staged Verification with Multiple Tools

Hints (steps):
1. For each phase, make the abstraction level and objective explicit, including what issue is to be eliminated.
2. Classify counterexamples as either holes in the abstraction or actual design defects.

Model answer (outline):
- Deliverables for Phases 1 to 3, such as specifications, models, and implementations, plus a classification of the issues found
- A consistency check of results across the tools

Self-review criteria:
- The relationship between abstraction level and discovered issues can be explained
- Deliverables are reproducible

## D.10 Chapter 9

### Basic Understanding Exercise 1: Formalizing Logical Inference

Hints (steps):
1. Symbolize propositions and map them to natural deduction rules such as introduction and elimination.
2. Treat inference 2 as a case in which a premise conflicts with real-world knowledge, that is, as an issue of exceptions.

Model answer (outline):
- A proof tree with the rule application order and an evaluation of validity
- The issue in inference 2: the premise `∀bird • canFly(bird)` is too strong for reality

Self-review criteria:
- The formalization is correct
- The problem can be explained as an error in the premise

### Basic Understanding Exercise 2: Basic Proofs in Rocq (formerly Coq)

Hints (steps):
1. The basic flow is `intros` followed by `split`, `left`, `right`, `destruct`, and `apply`.
2. Handle quantification with `intros x`, and build existence proofs with `exists x`.

Model answer (outline):
- A proof strategy, stated as a tactic sequence
- If necessary, define helper lemmas in advance, for example for the distribution of `forall`

Self-review criteria:
- The proof passes
- The strategy can be explained, including why those tactics were chosen

### Practical Exercise 1: Proving Properties of Data Structures

Hints (steps):
1. For append and reverse, structural induction such as `induction l1` is the basic technique.
2. First prepare helper lemmas such as `length_append`.

Model answer (outline):
- `append_assoc`: induct on `l1`, using `simpl` and `rewrite`
- `reverse_involutive`: use `reverse_append` as a helper lemma

Self-review criteria:
- The selection of helper lemmas is reasonable
- The proof remains readable and does not depend excessively on automation

### Practical Exercise 2: Proving Algorithm Correctness

Hints (steps):
1. Prove preservation of sortedness, such as `insert_sorted`, before proving global sortedness such as `insertion_sort_sorted`.
2. Separate correctness into sortedness and permutation.

Model answer (outline):
- A proof skeleton for `insert_sorted`
- A proof skeleton for `insertion_sort_permutation`, using permutation lemmas

Self-review criteria:
- Property decomposition is done appropriately
- The proof is sound and passes

### Advanced Exercise: A Practical Verification Project

Hints (steps):
1. Keep the target small and fix the properties to be proved, such as reversibility or invariant preservation.
2. Define the specification in `Prop` before the implementation and shape it so that the proofs can pass.

Model answer (outline):
- The chosen option and its specification, invariants, and proof plan
- A summary of discovered assumptions such as boundary conditions and data-type constraints

Self-review criteria:
- The scope is appropriate
- There is a practical takeaway about what can be reused

## D.11 Chapter 10

### Basic Understanding Exercise 1: Hoare Logic Fundamentals

Hints (steps):
1. For assignment, reason backward by substituting into the postcondition.
2. For conditionals, create a Hoare triple for each branch and compose them.
3. For loops, define an invariant and then prove initialization, preservation, and termination.

Model answer (outline):
- Task 1-1: `{True} x:=y+2; z:=x*3 {z=3*(y+2)}`; intermediate assertions may be included
- Task 1-2: focus on `result=|x|` in the branches
- Task 1-3: define an invariant such as `sum = (i-1)*i/2`

Self-review criteria:
- The invariant is correct and the reasoning is valid
- The precondition is neither too strong nor too weak

### Basic Understanding Exercise 2: Finding Loop Invariants

Hints (steps):
1. Use a property over the already-processed range as the invariant.
2. Show termination with a variant function such as the remaining number of elements.

Model answer (outline):
- Linear search: the relationship describing whether the target is absent from or present in positions before `i`
- Maximum search: `max` is the maximum of `array[0..i-1]`
- Insertion sort: in the outer loop, `0..i-1` is already sorted

Self-review criteria:
- The invariant satisfies initialization, preservation, and termination
- The variant function is reasonable

### Practical Exercise 1: Verifying Array Operations

Hints (steps):
1. Fix the specification first, with preconditions and postconditions. For sorting, that means both order and permutation.
2. Treat boundary conditions such as array bounds with the same importance as invariants.

Model answer (outline):
- The chosen algorithm and its specification, including correctness and termination
- The main invariants and the overall proof strategy

Self-review criteria:
- Properties are separated into correctness, termination, and safety
- The proof can be followed clearly

### Practical Exercise 2: Verification with a Tool

Hints (steps):
1. In tools such as `Dafny`, write `requires`, `ensures`, and `invariant` clauses first.
2. If verification does not pass, suspect that the invariant is too weak or incomplete.

Model answer (outline):
- Implementation code with specification annotations
- The verification execution log
- Difficulties encountered and the fixes applied, such as strengthening invariants and adding boundary conditions

Self-review criteria:
- Mechanical verification passes
- The fix process can be explained when verification initially fails

### Advanced Exercise: Partial Verification of a Practical System

Hints (steps):
1. Limit the target range and focus on roughly three properties.
2. Practical value increases if you can describe not only the specification but also the route into tests and CI integration.

Model answer (outline):
- The reason for selecting the target
- The properties, specification, and verification approach
- The issues discovered and the improvement proposals

Self-review criteria:
- The scope and properties are appropriate
- Practical deployment issues are stated clearly

## D.12 Chapter 11

### Reading Check Exercise 1: Evaluating an Adoption Strategy

Hints (steps):
1. Check whether the plan violates staged adoption, that is, starting small.
2. Reduce KPIs to measurable items such as reproduction rate, `MTTR`, and reduction of major incidents.

Model answer (outline):
- The problems in the plan, such as being too large, uniformly company-wide, or evaluated only in the short term
- A staged adoption proposal, such as pilot to broader rollout, together with KPIs

Self-review criteria:
- The plan is revised into a realistic one
- The KPIs are measurable

### Reading Check Exercise 2: Organizational Culture Analysis

Hints (steps):
1. Separate technical issues from cultural issues.
2. Break down resistance into causes such as increased workload, anxiety about evaluation, and skill differences.

Model answer (outline):
- Characteristics of the current culture
- Obstacles and enabling factors
- A change strategy involving education, standardization, and successful early experiences

Self-review criteria:
- The analysis is concrete
- The measures are executable

### Practical Exercise 1: ROI Analysis

Hints (steps):
1. Base the estimate on the difference in defect-fix cost when problems are eliminated earlier in the lifecycle.
2. Always state assumptions explicitly and include sensitivity analysis with plus and minus variation.

Model answer (outline):
- Assumptions and formulas
- Comparison of introduction cost against expected reduction effect
- Uncertainty tied to assumptions and the related risk

Self-review criteria:
- The calculation basis can be followed
- The validity of the assumptions can be explained

### Practical Exercise 2: Process Integration Design

Hints (steps):
1. Place checks across pull requests, nightly runs, and pre-release runs as in Figure 11-1.
2. Make artifact preservation and reproduction steps mandatory on failure.

Model answer (outline):
- Gate design, including mandatory and soft gates
- Exception flow, including approver, deadline, and rollback

Self-review criteria:
- Reproducibility and operations are assured
- The design does not make exceptions routine

### Advanced Exercise: Comprehensive Adoption Plan

Hints (steps):
1. Build a roadmap along three axes: people, process, and tools.
2. Eliminate failure patterns such as oversized introduction and tool fragmentation before they occur.

Model answer (outline):
- A one-year plan including stages, deliverables, and education
- Consensus building and governance

Self-review criteria:
- The execution plan is staged
- Governance is clear

## D.13 Chapter 12

### Reading Check Exercise 1: Tool Selection Matrix

Hints (steps):
1. Organize the fit between the problem domain, such as safety-critical, concurrent, or distributed work, and each method.
2. Include learning and operating cost and ease of CI integration as evaluation axes.

Model answer (outline):
- Candidate tools and the reasons for choosing them, considering requirements, constraints, and risks
- An 18-month staged plan from introduction to stable adoption

Self-review criteria:
- Evaluation axes are clear
- The plan is realistic

### Reading Check Exercise 2: CI/CD Integration Design

Hints (steps):
1. For pull requests, keep the minimum verification short, stable, and reproducible.
2. Use nightly runs to reduce false negatives and pre-release runs to confirm critical properties.

Model answer (outline):
- Job structure for pull requests, nightly runs, and pre-release checks
- Artifact preservation and exception approval

Self-review criteria:
- The staging is appropriate
- Counterexample handling is part of the design

### Practical Exercise 1: Code Generation Strategy

Hints (steps):
1. Treat generated artifacts as untrusted and close the loop with verifiers.
2. Keep specification diffs and implementation diffs synchronized.

Model answer (outline):
- Generation targets such as specifications, tests, and contracts, plus the review viewpoints
- The design of verification and CI gates

Self-review criteria:
- The trust boundary is clear
- Reproducibility is ensured

### Practical Exercise 2: Failure Analysis of Tool Introduction

Hints (steps):
1. Classify failure factors into technology, process, and organization.
2. Turn recurrence prevention into a checklist.

Model answer (outline):
- A classification of failure factors
- Improvement measures such as staged rollout, templates, and CI integration

Self-review criteria:
- Cause analysis is concrete
- Improvement measures are translated into operational practice

### Advanced Exercise: Designing an Integrated Toolchain

Hints (steps):
1. Manage deliverables across tools, including specifications, logs, and counterexamples, in a common format.
2. Use caching and pinned versions to preserve reproducibility.

Model answer (outline):
- A toolchain configuration diagram
- Pinned dependencies, artifacts, and exception flow

Self-review criteria:
- Reproducibility can be explained
- Operating cost is realistic

## D.14 Chapter 13

### Reading Check Exercise 1: Comparative Analysis of Case Studies

Hints (steps):
1. Build a comparison table across technical, organizational, economic, and external factors.
2. Separate lessons that can be copied from context-specific factors.

Model answer (outline):
- A comparison table
- Common success factors and differences
- Viewpoints for deciding applicability

Self-review criteria:
- Comparison axes are systematic
- Lessons are generalized appropriately

### Reading Check Exercise 2: Industry Applicability Analysis

Hints (steps):
1. Industries with stronger regulation, safety requirements, and failure models usually offer higher adoption value.
2. Start from areas that can be verified in small scope.

Model answer (outline):
- Risks in the target industry and candidate application areas
- Introduction steps and KPIs

Self-review criteria:
- Industry characteristics are reflected
- Adoption is staged

### Practical Exercise 1: Detailed Case Investigation

Hints (steps):
1. Reference at least three primary or quasi-primary sources and attach a citation to each claim.
2. Write both what was guaranteed, that is, the properties, and how it can be reproduced in a minimum setup.

Model answer (outline):
- A source list
- A summary of properties and reproduction steps

Self-review criteria:
- Sources are appropriate
- Reproducibility is demonstrated

### Practical Exercise 2: Designing an Adoption Plan

Hints (steps):
1. Select targets according to criticality.
2. Include CI integration and exception flow in the plan.

Model answer (outline):
- Target selection, verification method, staged introduction, and KPIs

Self-review criteria:
- The plan is realistic
- Guardrails are present

### Advanced Exercise: Future Scenario Analysis

Hints (steps):
1. Build multiple scenarios under assumptions such as technological progress in AI and verification automation and stronger regulation.
2. Separate uncertainty as hypothesis, and state the basis through sources and assumptions.

Model answer (outline):
- Two or three scenarios, together with assumptions, impact, and response measures

Self-review criteria:
- Hypotheses and facts are separated
- The implications are usable in practice

## D.15 Documentation Template for AI Use (Common)

Treat AI output as a proposal, and let the verifier determine pass or fail. The
working record should include the following.

- The prompts used, including requirements and constraints
- The generated specifications and invariants
- Verification commands and logs, including seed, depth, scope, and elapsed time
- If a counterexample appears, the fix history including the diff and the re-verification log

Example record format:

```
## Prompts Used
...

## Generated Specification
...

## Verification Log
command: ...
seed: ...
depth/scope: ...
result: ...

## Counterexample and Fix
counterexample: ...
fix: ...
recheck: ...
```
