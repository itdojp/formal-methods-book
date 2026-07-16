---
layout: book
title: "Chapter 8: Introduction to Model Checking"
description: "Automated verification, state-space exploration, and counterexamples."
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter08.md"
translation_status: "partial"
translation_source_commit: "5b852a65db6c70440b98a6648136fd5c55e00e7a"
translation_reviewed_at: "2026-07-16"
translation_tracking_issue: "https://github.com/itdojp/formal-methods-book/issues/328"
---
# Chapter 8: Introduction to Model Checking

> **Translation status: Partial.** Reviewed against Japanese source commit [`5b852a65db6c`](https://github.com/itdojp/formal-methods-book/commit/5b852a65db6c70440b98a6648136fd5c55e00e7a) on 2026-07-16.
> Some content, headings, examples, tables, or references remain partially synchronized. [Track the remaining work](https://github.com/itdojp/formal-methods-book/issues/328).

## 8.1 The Dream of Automated Verification: Letting Computers Prove Correctness

### Human Limits and Machine Capability

As software systems become more complex, it becomes increasingly difficult to
guarantee correctness through human intuition and experience alone. Developers
write code, reviewers inspect it, and testers execute it, but subtle bugs and
unexpected interactions still slip through.

Model checking complements these cognitive limits with computation. For a
specified finite-state model, it systematically explores executions reachable
from the configured initial states and checks the selected properties. Its
exhaustiveness is relative to that model, property, search method, and
configuration, not to the implementation and physical environment as a whole.

The key innovation of model checking is automated checking and counterexample
search. Once the model and properties are described, a checker either confirms
the property for its completed scope or produces a violating trace. A timeout,
`unknown`, resource exhaustion, bounded run, or approximate run is not the same
as confirmation.

### The Power of Exhaustive Exploration

The basic idea behind model checking is brute-force exploration of the system's
state space. At first glance this may appear inefficient, but in practice it is
extremely powerful.

Like search-based game programs, model checkers traverse mechanically defined
states and transitions. Neither class of program enumerates every real-world
possibility without limits; the modeled state space and configuration determine
what is searched. In verification, a reproducible result is therefore either a
counterexample or evidence that no violation was found in the completed scope.
The latter does not cover inputs, implementation details, or failures omitted
from the model.

### Automating Formal Verification

Before model checking became practical, formal verification relied primarily on
manual theorem proving. Experts advanced one proof obligation at a time through
mathematical reasoning. The method was theoretically strong, but it had clear
practical limits:

- **Demand for expertise**: advanced mathematical background was required
- **Time and cost**: large proofs often took a long time
- **Human fallibility**: hand-written proofs can themselves contain mistakes
- **Scalability limits**: large systems were difficult to handle

Model checking changed the situation fundamentally. A team no longer needed to
master every proof detail. If the system model and target properties could be
described precisely, verification became possible.

### The Educational Value of Counterexamples

One of the most valuable features of model checking is the counterexample it
provides when a property does not hold. Instead of returning only an abstract
"incorrect," it explains *under what circumstances the problem occurs*.

For system designers, counterexamples are highly actionable:

- **Concrete problem framing**: an abstract issue becomes a concrete scenario
- **Cause identification**: the root cause can be traced
- **Repair guidance**: the failure point becomes visible
- **Deeper understanding**: system behavior becomes easier to reason about

### Improving Quality Through Early Detection

Model checking can discover problems early in development. By checking designs
or specifications before implementation, teams can reduce the number of defects
found only after code is written.

The cost of fixing a bug generally rises the later it is discovered. Common
industry estimates say that if a defect found in requirements costs 1 unit to
fix, the same defect may cost 5 units in design, 10 in implementation, 20 in
testing, and over 100 in production. The actual multiplier depends on the
organization, domain, and process, but the direction is consistent.

Early defect detection through model checking is therefore not only a technical
advantage but also a cost-control mechanism.

![Figure 8-1: The overall process of model checking]({{ '/assets/images/diagrams/model-checking-process-en.svg' | relative_url }})

### Understanding the Limits Correctly

Model checking is powerful, but it is not universal. Using it effectively
requires understanding its limits:

- **The state-explosion problem**: the number of states can grow
  exponentially, making verification difficult
- **The need for abstraction**: real systems must be abstracted into finite
  models
- **The difficulty of property specification**: teams need skill in writing
  formal properties
- **Effects of abstraction and search mode**: over-approximation can produce
  behaviors absent from the implementation, while under-approximation, bounded
  search, and approximate search can miss violations outside their scope
- **Distinct completion results**: completion, counterexample, timeout,
  `unknown`, and resource exhaustion must not be reported as one kind of success

Practical model checking depends on choosing an appropriate abstraction level
and a verification strategy that matches the problem. Reports should record
the model and property, tool version, fairness, bounds, approximation mode,
timeout, and completion status.

### Industrial Success Stories

Model checking is no longer only an academic technique. It has a substantial
record in industry:

- **Intel** uses formal verification in processor design and has found bugs
  beyond the reach of conventional simulation
- **Microsoft** has applied verification to Windows drivers and reduced serious
  failures such as blue-screen crashes
- **Amazon** is well known for using TLA+ and model-checking-oriented thinking
  when designing distributed systems
- **Airbus** uses formal techniques to support assurance arguments for
  safety-critical control systems

These cases show that model checking has matured from a research method into a
practical engineering tool.

### Connecting to the Alloy Models in Chapter 4

The Alloy modeling you studied in Chapter 4 is an excellent introduction to
model checking. Alloy's `check` command is, in essence, a small-scale form of
model checking:

Pseudo notation (the Chapter 4 model definitions are omitted, so this fragment
cannot be executed as-is):

```alloy
// Revisiting the email-system example from Chapter 4
assert NoUnauthorizedAccess {
    all u: User, e: Email |
        some e.confidential and
        u != e.sender and u not in e.recipients and
        u != e.confidential and
        AdminAccess not in u.roles.permissions
        implies
        not canReadEmail[u, e]
}
check NoUnauthorizedAccess for 5 User, 5 Email, 3 Role
```

In this `check` operation, Alloy explores all possible states within the given
scope and searches for a counterexample. That is the same core idea you study
in this chapter.

### Democratizing Formal Verification

One of model checking's most important contributions is the *democratization*
of formal verification. What used to be accessible only to a small number of
specialists has become a comparatively learnable tool for a broader range of
engineers.

That shift changes formal methods from a niche academic technique into a
practical development tool. Over time, model checking is likely to become a
standard part of software quality assurance.

## 8.2 State Spaces and How to Explore Them

### State Space as a Conceptual Framework

A *state space* is the set of all states a system can possibly take. This
mathematical abstraction lets us understand even complex software as a finite
or countably infinite collection of points.

Consider a running program. The program counter, variable values, memory
contents, input/output status, and other runtime information together form the
current state. Execution can then be understood as a trajectory through that
state space.

This idea is analogous to phase spaces in physics and other mathematical
representations of dynamical systems. By recasting dynamic behavior as a static
structure, we gain something we can analyze.

### Structure of a State-Transition Graph

The structure of a state space is usually visualized as a *state-transition
graph*. In such a graph, nodes represent states and edges represent
transitions.

Pseudo notation:

```text
Initial state -> State 1 -> State 2 -> State 3
      |             |          |          |
   State A ->    State B -> State C -> State D
      |             |          |          |
   State X ->    State Y -> State Z -> Final state
```

This structure lets us reason about important system properties:

- **Reachability**: can one state reach another?
- **Cyclicity**: does the system contain persistent loops?
- **Deadlock**: is there a state from which no progress is possible?
- **Liveness**: is some kind of forward movement always possible?

### Exploding State Counts

In real software systems, the number of states grows explosively. This is the
best-known challenge in model checking: the *state-explosion problem*.

Consider a simple example with three Boolean variables:

- `a`, `b`, `c ∈ {true, false}`
- Number of possible states = `2^3 = 8`

If the system has ten Boolean variables:

- Number of possible states = `2^10 = 1,024`

With 32 Boolean variables:

- Number of possible states = `2^32 ≈ 4.3 × 10^9`

Real programs also contain integers, arrays, pointers, buffers, counters, and
various control states. A single 64-bit integer variable already allows
`2^64 ≈ 1.8 × 10^19` values.

### Reachability Analysis

Not every state is reachable during actual execution. Model checking therefore
focuses on *reachable states*, that is, states reachable from the initial
state. This reduces the search space to some extent.

Pseudo notation:

```text
Reachable <- {InitialStates}
Frontier <- {InitialStates}
while Frontier != {} do
    NewStates <- {}
    for each state s in Frontier do
        for each successor t of s do
            if t not in Reachable then
                NewStates <- NewStates union {t}
                Reachable <- Reachable union {t}
    Frontier <- NewStates
```

This is breadth-first exploration of the reachable state space.

### Depth-First Versus Breadth-First Search

State-space exploration typically uses one of two basic strategies.

**Depth-first search (DFS)**:

- **Advantage**: low memory usage
- **Disadvantage**: may fail to find the shortest counterexample
- **Typical use**: cycle detection and deadlock detection

**Breadth-first search (BFS)**:

- **Advantage**: finds the shortest counterexample
- **Disadvantage**: high memory usage
- **Typical use**: minimum-step reachability analysis

Practical tools often switch strategies or combine them depending on the
verification objective.

### Efficient State Representation

Representing and managing huge numbers of states efficiently is essential for
practical model checking.

**Bit-vector representation**:

Pseudo notation:

```text
State = [a:1, b:0, c:1, counter:5]
-> Bit vector = 10100101
```

**Hash tables**:
Visited states are typically stored in hash tables to support fast lookup.

**Compression**:
Similar states or infrequent patterns can sometimes be compressed to save
memory.

### Partial Order Reduction

In concurrent systems, different execution orders can lead to the same result.
*Partial order reduction* exploits this redundancy.

Suppose two operations `A` and `B` are independent:

- execution order `A -> B`
- execution order `B -> A`

If both produce the same outcome, it is unnecessary to explore both. By
keeping only a representative ordering, the tool reduces the state count.

### Symbolic Model Checking

Traditional explicit-state model checking stores states one by one. Symbolic
model checking represents *sets of states* with logical formulas, often using
BDD (Binary Decision Diagram) structures.

Pseudo notation:

```text
State set {(a=1,b=0), (a=1,b=1), (a=0,b=1)}
-> BDD form: (a and not b) or (a and b) or (not a and b)
-> Reduced: a or (not a and b) = a or b
```

When the structure is favorable, symbolic methods can represent extremely
large state sets compactly.

### Iterative Deepening

To balance completeness and memory constraints, tools sometimes use iterative
deepening.

Pseudo notation:

```text
for depth = 1 to MaxDepth do
    result = DepthLimitedSearch(depth)
    if result = "property violation" then
        return counterexample
    if result = "complete" then
        return "property verified"
```

This expands the search horizon gradually while keeping memory under control.

### Parallel and Distributed Exploration

Modern multi-core processors and distributed environments make it possible to
parallelize state-space exploration.

**Work-stealing**:

Pseudo notation:

```text
Each thread keeps its own stack.
When one thread runs out of work,
it steals work from another thread.
```

**Distributed hash tables**:
States are partitioned across multiple machines and explored cooperatively over
the network.

These techniques make it possible to verify systems that were previously too
large to handle.

## 8.3 Describing Properties with Temporal Logic

### The Challenge of Expressing Dynamic Properties

The correctness of a software system cannot be judged from a single snapshot.
What matters is how the system behaves over time. Properties such as "every
request is eventually answered," "deadlock never occurs," and "resources are
distributed fairly" all concern dynamic behavior.

Temporal logic is the language used to describe such behavior precisely.
Ordinary logic talks about the current state. Temporal logic talks about how
states evolve over time.

### CTL: The World of Computation Trees

CTL (Computation Tree Logic) is one of the most widely used logics in model
checking. It treats execution as a *computation tree*: each node is a state,
each edge is a transition, and the branching structure represents alternative
futures.

Pseudo notation:

```text
          Initial state
         /      |      \
     State 1  State 2  State 3
      /  \      /  \      /  \
    ... ...   ... ...   ... ...
```

CTL formulas combine *path quantifiers* with *temporal operators*.

**Path quantifiers**:

- **A** (All paths): for all execution paths
- **E** (Exists path): for at least one execution path

**Temporal operators**:

- **X** (neXt): in the next state
- **F** (Future): at some point in the future
- **G** (Globally): always
- **U** (Until): until

### Practical CTL Examples and Their Intuition

**Safety**:

Pseudo notation:

```ctl
AG(!error)
```

"Along all execution paths, an error never occurs."

**Liveness**:

Pseudo notation:

```ctl
AG(request -> AF(response))
```

"Along all execution paths, whenever a request exists, a response eventually
occurs."

**Reachability**:

Pseudo notation:

```ctl
EF(goal_achieved)
```

"There exists an execution path on which the goal is eventually reached."

**Fairness-oriented intuition**:

Pseudo notation:

```ctl
AG(EF(process1_scheduled) & EF(process2_scheduled))
```

"At every point, there remains a future in which both process 1 and process 2
can eventually be scheduled."

### LTL: The View of Linear Time

LTL (Linear Temporal Logic) takes a different perspective. It treats execution
as a *single line of time* rather than a branching tree.

**Basic LTL operators**:

- **○** (Next): at the next moment
- **◇** (Eventually): eventually
- **□** (Always): always
- **U** (Until): until

**Examples of LTL formulas**:

Pseudo notation:

```ltl
□(request -> ◇response)
"Always, if there is a request, there is eventually a response."

□◇(process_scheduled)
"The process is scheduled infinitely often."

◇□(stable)
"Eventually the system becomes stable and stays stable thereafter."
```

### Differences in Expressive Power Between CTL and LTL

CTL and LTL are suited to different classes of properties.

**A property that CTL expresses well**:

Pseudo notation:

```ctl
AG(EF(reset_possible))
```

"It is always the case that there exists a path to a state in which reset is
possible."

This cannot be expressed directly in LTL.

**A property that LTL expresses well**:

Pseudo notation:

```ltl
□(grant1 -> (!grant2 U release1))
```

"Once process 1 is granted access, process 2 is not granted access until
process 1 releases it."

This kind of ordering-oriented mutual exclusion property is much more natural
in LTL than in CTL.

### Practical Property Patterns

Several property patterns appear again and again in real verification tasks.

**Mutual exclusion**:

Pseudo notation:

```ctl
AG(!(critical1 & critical2))
```

"The two processes are never in their critical sections at the same time."

**Deadlock freedom**:

Pseudo notation:

```ctl
AG(EX(true))
```

"From every reachable state, there is at least one next state."

**Starvation freedom**:

Pseudo notation:

```ltl
□(waiting -> ◇served)
```

"A waiting process is eventually served."

**Ordering constraints**:

Pseudo notation:

```ltl
□(event_a -> ○(!event_b U event_c))
```

"After event `a`, event `b` must not occur until event `c` occurs."

### Hierarchical Structure of Properties

Complex systems benefit from organizing properties hierarchically.

**Level 1: Basic state validity**:

Pseudo notation:

```ctl
AG(valid_state)
```

"The system is always in a valid state."

**Level 2: Protocol correctness**:

Pseudo notation:

```ctl
AG(message_sent -> AF(ack_received))
```

"Every sent message is eventually acknowledged."

**Level 3: Performance-oriented properties**:

Pseudo notation:

```ctl
AG(request -> AF<=n(response))
```

"A response arrives within at most `n` time units."

### Negated Properties and Counterexamples

Counterexamples are central to model checking.

If `AG(safe)` does not hold:

- the counterexample is a path from an initial state to an unsafe state
- equivalently, some execution satisfies `EF(!safe)`

If `AF(goal)` does not hold:

- the counterexample is an infinite path that never reaches the goal
- equivalently, some execution satisfies `EG(!goal)`

### Why Fairness Constraints Matter

Realistic verification often requires fairness assumptions. Without them, tools
may spend effort on executions that are theoretically possible but irrelevant
to the system's intended environment.

**Weak fairness (concept)**: exclude executions in which an action remains
continuously enabled from some point onward, yet is ignored forever.

**Strong fairness (concept)**: exclude executions in which an action becomes
enabled infinitely often, yet is avoided every time.

In practical tools, fairness usually appears as a constraint on the set of
paths to be considered. In this chapter, we use the SMV-style forms
`FAIRNESS` (justice) and `COMPASSION (p, q)` as conceptual notation. The
surrounding module and variable declarations required by real tools are omitted
unless stated otherwise.

Example (NuSMV/nuXmv fairness constraints):

Pseudo notation:

```smv
FAIRNESS running_i
COMPASSION (enabled_a, executed_a)
```

Summary of the meaning:

- `FAIRNESS p`: only evaluate paths on which `p` is true infinitely often
- `COMPASSION (p, q)`: only evaluate paths on which infinite occurrences of
  `p` imply infinite occurrences of `q`

For the temporal-logic meaning of fairness and the precise TLA+ treatment, see
also Chapter 7, "Temporal Expressions of Fairness."

Minimal NuSMV/nuXmv example with `FAIRNESS` and `COMPASSION`:

【Context-dependent snippet】
```smv
MODULE main
VAR
  enabled_a : boolean;
  executed_a : boolean;

ASSIGN
  init(enabled_a) := FALSE;
  init(executed_a) := FALSE;
  next(enabled_a) := !enabled_a;
  next(executed_a) := enabled_a;

FAIRNESS enabled_a
COMPASSION (enabled_a, executed_a)
```

For a self-contained file, see `examples/ch08/nusmv/fairness.smv`.

Notes:

- `FAIRNESS enabled_a` limits attention to paths on which `enabled_a` is true
  infinitely often.
- `COMPASSION (enabled_a, executed_a)` limits attention to paths on which
  infinitely many `enabled_a` states imply infinitely many `executed_a`
  states.
- In this minimal model, `enabled_a` alternates between `TRUE` and `FALSE`,
  and `executed_a` follows it with a one-step lag.
- In general, fairness constraints narrow the set of explored paths. They do
  not, by themselves, state a liveness property.

### Practical Guidelines for Writing Properties

Effective property descriptions usually follow a few principles:

1. **Be concrete and checkable**: avoid ambiguity and refer to explicit states
   and events
2. **Refine incrementally**: start with simple properties and grow toward more
   complex ones
3. **Think about counterexamples**: decide whether a violating trace would
   truly indicate a defect
4. **Use realistic assumptions**: avoid idealized properties that the system
   cannot actually satisfy

### Tool-Specific Extensions

Real model-checking tools often provide practical extensions on top of standard
temporal logic.

**Example in SPIN / Promela**:

【Context-dependent snippet】
```promela
bool critical_section = false;
bool cs1 = false;
bool cs2 = false;

active proctype Worker() {
    do
    :: critical_section = true;
       critical_section = false
    od
}

active proctype P1() {
    do
    :: atomic { !cs2 -> cs1 = true; cs1 = false }
    od
}

active proctype P2() {
    do
    :: atomic { !cs1 -> cs2 = true; cs2 = false }
    od
}

ltl fairness { []<>(critical_section) }
ltl mutual_exclusion { [](!(cs1 && cs2)) }
```

For a self-contained file, see `examples/ch08/spin/ltl-properties.pml`.

**Example in NuSMV / SMV**:

Pseudo notation:

```smv
LTLSPEC G(request -> F(response))
CTLSPEC AG(critical1 -> !critical2)
```

These extensions turn theoretical temporal logic into something directly useful
for engineering verification.

## 8.4 State Explosion: Compromising with Reality

### The Mathematical Reality of Combinatorial Explosion

The state-explosion problem is the most fundamental challenge in model
checking. Its severity is often underestimated until one looks at concrete
numbers.

Suppose there are `n` processes and each process has `k` local states:

- total number of states = `k^n`

With 10 processes and 3 states each:

- total number of states = `3^10 = 59,049`

With 20 processes and 3 states each:

- total number of states = `3^20 ≈ 3.5 × 10^9`

If we also add time, message queues, counters, buffers, and local variables,
the state count becomes astronomical. Even today's fastest machines cannot
fully enumerate such spaces in many cases.

### The Physical Limit of Memory

Model checking usually requires storing visited states. If each state takes 100
bytes:

- `10^6` states = `100 MB`
- `10^9` states = `100 GB`
- `10^12` states = `100 TB`

Handling `10^12` states would require around one hundred terabytes of memory,
which is not a realistic target for ordinary engineering workflows.

### Root Causes of State Explosion

Understanding why state explosion happens helps us choose the right mitigation
techniques.

**Explosion caused by concurrency**:

Pseudo notation:

```text
2 processes, each with 10 states -> 100 states
3 processes, each with 10 states -> 1,000 states
10 processes, each with 10 states -> 10^10 states
```

**Explosion caused by data values**:

Pseudo notation:

```text
1 variable of type 32-bit integer -> 2^32 ≈ 4.3 billion possibilities
1 variable of type 64-bit integer -> 2^64 ≈ 1.8 x 10^19 possibilities
```

**Explosion caused by dynamic data structures**:
Lists, trees, graphs, and other dynamic structures combine size and shape, so
the number of states grows extremely quickly.

### Abstraction: Strategically Omitting Detail

The most basic response to state explosion is abstraction. The idea is to omit
details that are irrelevant to the property being checked and keep only the
information that matters.

**Data abstraction**:

Pseudo notation:

```text
Concrete value: balance = 1247
-> Abstract value: balance in {zero, positive, negative}

Concrete value: array[100]
-> Abstract value: array_size in {empty, small, large}
```

**Control abstraction**:

Pseudo notation:

```text
Concrete control flow: a complex algorithm
-> Abstract control flow: success / failure
```

### Bounded Model Checking

Bounded model checking controls explosion by limiting the search depth.

**Basic idea**:

- explore only states reachable within `k` steps
- if a violation is found within `k` steps, the answer is negative
- if no violation is found, the result is only "no bug was found within this
  bound"

**Advantages**:

- memory consumption is easier to control
- SAT solvers and related engines can be used effectively
- discovered counterexamples are often short and easy to understand

**Limitations**:

- completeness is not guaranteed
- choosing a good bound `k` is difficult

### The Theory and Practice of Partial Order Reduction

In concurrent systems, many action interleavings do not affect the final
result. Partial order reduction exploits this redundancy.

Pseudo notation:

```text
Process 1: x := x + 1
Process 2: y := y + 1
```

These operations are independent. The orders `(1 -> 2)` and `(2 -> 1)` lead to
the same result, so only one representative ordering needs to be explored.

When there are `n` independent actions:

- naive exploration can consider `n!` orders
- partial order reduction may keep only one representative order

### Symbolic Model-Checking Techniques

Symbolic model checking uses formulas to represent state sets and performs set
operations through logic operations.

Pseudo notation:

```text
State set S = {(x=0,y=0), (x=0,y=1), (x=1,y=1)}
-> BDD form: (!x and !y) or (!x and y) or (x and y)
-> Reduced: !x or (x and y)
```

When BDDs are effective, exponentially large state sets can sometimes be
handled with polynomial-size structures.

Modern verification also relies heavily on SAT and SMT solvers. By encoding
transitions as logical constraints and handing them to the solver, tools can
explore large bounded spaces efficiently.

### Compositional Verification

Large systems can often be decomposed into smaller parts, verified separately,
and then reasoned about compositionally.

Pseudo notation:

```text
Component A: guarantees QA under assumption PA
Component B: guarantees QB under assumption PB
Whole system: (PA and PB) -> (QA and QB)
```

This keeps each verification unit smaller while still supporting claims about
the overall system.

### Iterative Refinement

If an abstraction is too coarse, it may produce a *spurious counterexample*.
One practical response is iterative refinement.

Pseudo notation:

```text
1. Verify with a coarse abstraction
2. If a counterexample appears, check whether it is real
3. If it is spurious, refine the abstraction
4. Return to step 1
```

This process gradually converges toward the minimum level of detail needed for
the target property.

### Parallel and Distributed Verification

Modern verification engines exploit multi-core processors and clusters.

**Parallel search strategies**:

- **work stealing**: each thread explores locally and load is redistributed
  dynamically
- **hash-based partitioning**: states are assigned to workers according to a
  hash

**Distributed verification**:

- one verification run spans multiple machines
- machines exchange state information over the network
- a distributed hash table tracks visited states

### Probabilistic and Quantitative Model Checking {#probabilistic-quantitative-model-checking}

The word *probabilistic* is used for at least two different techniques.
Statistical model checking randomly samples paths from a very large state space and **estimates** a property.
Probabilistic model checking instead gives the transitions themselves probabilities or rates and **computes** reachability probabilities, steady-state probabilities, and expected costs.
This section focuses on the latter; it is not merely randomized exploration order.

Ordinary model checking asks Boolean questions such as whether safety holds on every execution in scope.
Probabilistic model checking adds questions such as these:

- What is the probability of eventually succeeding?
- Is the failure probability below an acceptable threshold?
- What is the long-run probability of being in a failed state?
- What is the expected retry count, time, energy, or cost before completion?

The first three PRISM model types to distinguish are the following.

| Model | Meaning of a transition | Typical question | Nondeterminism |
| --- | --- | --- | --- |
| DTMC (discrete-time Markov chain) | Select the next state from a probability distribution at each step | Retry counts, discrete rounds, randomized algorithms | None |
| CTMC (continuous-time Markov chain) | Transition rates induce exponentially distributed waiting times | Time-bounded reliability, failure and repair, performance | None |
| MDP (Markov decision process) | An action is chosen nondeterministically, then a probability distribution selects the successor | Best- and worst-case values under control or environment choices | Resolved by a scheduler/adversary |

A DTMC step must not be interpreted as one second without justification.
A CTMC that represents physical time needs explicit rates and time units.
For an MDP, define how the scheduler resolves choices and usually inspect worst- and best-case bounds with `Pmin` / `Pmax` or `Rmin` / `Rmax` rather than reporting one unexplained value.

PRISM's property language supports PCTL-style properties for DTMCs and MDPs and CSL-style properties for CTMCs.
A reader does not need the complete logics to read these minimum forms.

| Property | Reading |
| --- | --- |
| `P>=0.99 [ F "success" ]` | Is the probability of eventually reaching `success` at least 0.99? |
| `P=? [ F "failure" ]` | Compute the probability of eventually reaching `failure`. |
| `S=? [ "success" ]` | Compute the long-run steady-state probability of being in `success`. |
| `R{"cost"}=? [ F "done" ]` | Compute expected accumulated `cost` before reaching `done`. |

`P=?` is a quantitative query, whereas `P>=...` checks a threshold.
`S` describes long-run behavior, and `R` evaluates rewards attached to states or transitions.
A reward need not be desirable: it can represent attempts, latency, energy, or monetary cost.
A reachability reward can be infinite when the target is missed with positive probability, so reachability must be checked as well.

**Self-contained retry-communication example**

The teaching DTMC assumes that every attempt succeeds independently with probability 0.8 and that the operation stops after at most three attempts.
Its canonical assets are [examples/prism/retry-communication/retry-communication.pm](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/prism/retry-communication/retry-communication.pm), [examples/prism/retry-communication/retry-communication.props](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/prism/retry-communication/retry-communication.props), and [examples/prism/retry-communication/expected-results.json](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/prism/retry-communication/expected-results.json).
With the PRISM 4.10.1 explicit engine, the failure probability is `0.2^3 = 0.008`, the success absorption and steady-state probability is `1 - 0.008 = 0.992`, and the expected attempt count is `1 + 0.2 + 0.2^2 = 1.24`.
The threshold property is `true` because `0.992 >= 0.99`.
The wrapper accepts the floating-point output `0.007999999999999995` within tolerance `1e-12` and records measured values in a JSON artifact.

<!-- example-contract: prism-retry-communication -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id prism-retry-communication
```

This contract runs in the `nightly` lane with PRISM 4.10.1 and the SHA-256-pinned official Linux x86-64 archive.
CI does not redistribute the tool binary through artifacts or Pages; it retains input hashes, standard output, and the expected-value comparison only.

**Checks that prevent overclaiming**

1. **Model assumptions**: The 0.8 success probability and independence between attempts are teaching assumptions. They cannot support a production reliability claim without measurements, operating conditions, correlations, and burst-failure analysis.
2. **State-space truncation**: The three-attempt cap makes the model finite, but it is not an unlimited-retry result. Vary the cap and inspect sensitivity.
3. **Parameter sensitivity**: Sweep `P_SUCCESS`, the attempt cap, repair rates, and costs over justified ranges to see whether the decision depends on one point estimate.
4. **Numerical precision**: Ordinary PRISM checks may build the full finite model and use iterative floating-point numerical methods. Record the engine, convergence criterion, and tolerance. PRISM also has limited arbitrary-precision exact-model-checking support, but ordinary output is not automatically a mathematically exact value.
5. **Scheduler/adversary**: Randomly resolving an MDP's nondeterminism during sampling does not evaluate the worst-case scheduler. Safety decisions need the `min` / `max` bounds and the scheduler assumptions.

Ordinary numerical model checking constructs the in-scope finite model and computes the property with methods such as linear-system solving or value iteration.
Simulation or statistical model checking samples random paths and depends on sample count, confidence, error width, and maximum path length.
Rare events can require very many samples, and random MDP choice resolution does not represent an adversarial bound.
Simulation is therefore useful for exploring large models, checking assumptions, and obtaining approximations, but it does not unconditionally replace numerical model checking.

> **Guarantee boundary**: Correct computation of a property by PRISM and validity of the real-world probability model are different claims.
> The former is reproducible from the tool version, input hashes, engine, and results; the latter requires data provenance, explicit assumptions, sensitivity analysis, and domain review.

### Choosing a Practical Strategy

In real projects, combinations of techniques work better than any one method.

**A staged approach**:

1. use bounded model checking to find easy bugs quickly
2. use abstraction to verify the most important properties
3. add symbolic or parallel techniques when scale requires them

**Cost-benefit analysis**:

- verification cost versus the value of the defects found
- completeness versus acceptable runtime
- automation versus the need for human intervention

State explosion cannot be eliminated completely. The engineering task is to
understand the system's structure and choose techniques that make verification
practical.

## 8.5 Interpreting and Using Counterexamples

### Counterexamples as a Gift

In model checking, a counterexample is more than an error report. It is a gift
that reveals a hidden defect in a concrete and inspectable form. Instead of
saying only "the specification is violated," the tool shows *how* the problem
arises and in *what sequence of states*.

Skilled designers learn from counterexamples at multiple levels. They do not
stop at "fix this bug." They also ask why the problem was possible, which
assumption failed, and whether similar defects exist elsewhere.

### Anatomy of a Counterexample

A typical counterexample contains the following elements:

1. **Execution trace**: a sequence of states from the initial state to the
   violating state
2. **State information**: the values of relevant variables in each state
3. **Transition information**: the action that caused each step
4. **Logical time**: the position of each step in the trace

Example: a mutual-exclusion violation

Pseudo notation:

```text
State 0: (Initial)
  process1_state = "thinking"
  process2_state = "thinking"
  flag1 = false, flag2 = false
  turn = 1

State 1: (Process 1 wants to enter)
  process1_state = "trying"
  process2_state = "thinking"
  flag1 = true, flag2 = false
  turn = 1

State 2: (Process 2 wants to enter)
  process1_state = "trying"
  process2_state = "trying"
  flag1 = true, flag2 = true
  turn = 1

State 3: (Both enter the critical section - VIOLATION!)
  process1_state = "critical"
  process2_state = "critical"
  flag1 = true, flag2 = true
  turn = 1
```

### Root-Cause Analysis

Finding the root cause of a counterexample requires systematic analysis.

**1. Identify the symptom**:

- what differs from the intended behavior?
- at what point does the defect become visible?

**2. Check the preconditions**:

- what conditions were necessary for the failure?
- why did those conditions hold?

**3. Analyze timing**:

- did the failure require a specific interleaving?
- would other timings cause the same issue?

**4. Revisit design decisions**:

- was the underlying design assumption valid?
- could another design avoid the problem entirely?

### Analyzing Deadlock Counterexamples

Deadlock counterexamples are especially educational.

Pseudo notation:

```text
State N: (Deadlock detected)
  Process A: waiting for Resource 2, holding Resource 1
  Process B: waiting for Resource 1, holding Resource 2
  Available resources: none
  Possible transitions: none
```

Points to analyze:

- **Formation of circular waiting**: in what order were resources acquired?
- **Avoidability**: at what point could a different choice have prevented the
  deadlock?
- **Design improvement**: would resource ordering or timeouts eliminate it?

### Analyzing Temporal-Property Violations

Violations of temporal properties often require deeper analysis.

Example of a liveness violation: "every request is eventually answered" fails.

Pseudo notation:

```text
Counterexample: an infinite loop that never generates a response
State 0 -> State 1 -> State 2 -> State 1 -> State 2 -> ...
```

Useful analysis steps:

- **find the strongly connected component** that forms the loop
- **check fairness assumptions** to see whether an enabled response action is
  being postponed forever
- **inspect external conditions** that may be preventing progress

### Handling Spurious Counterexamples

Abstraction can produce counterexamples that cannot occur in the real system.
These are called *spurious counterexamples*.

Typical signs:

- they depend on information lost by abstraction
- they include transitions that are impossible at implementation level
- they assume unrealistic timing or impossible combinations of conditions

Responses:

1. **refine the abstraction** to preserve more information
2. **add constraints** to remove unrealistic transitions
3. **replay the trace concretely** in the original system or a more detailed
   model

### Counterexample Minimization

Long counterexamples are hard to understand, so minimization matters.

Common techniques:

- **binary search over the trace** to remove unnecessary segments
- **causal analysis** to retain only steps directly related to the failure
- **state projection** to focus on the relevant variables only

Pseudo notation:

```text
Original counterexample: 50 steps
Minimized counterexample: 8 steps (only essential transitions)
```

### Visualizing Counterexamples

Complex counterexamples become easier to interpret when visualized well.

**State-transition view**:

Pseudo notation:

```text
[State0] --action1--> [State1] --action2--> [State2]
    |                     |                     |
  var1=0               var1=1               var1=2
  var2=false           var2=false           var2=true
```

**Timeline view**:

Pseudo notation:

```text
Process A: |----thinking----|--trying--|--critical--|
Process B: |----thinking----|----trying----|--critical--|
Time:      0              5           10           15
```

**Message-sequence view**:

Pseudo notation:

```text
Client    Server    Database
  |         |          |
  |--req--->|          |
  |         |--query-->|
  |         |<--resp---|
  |<--err---|          |
```

### Learning and Improving from Counterexamples

The point of counterexample analysis is not only to fix one bug but to improve
the system as a whole.

**Pattern recognition**:

- are similar problems present elsewhere?
- did the same design choice contribute to multiple issues?
- is a broader design correction needed?

**Preventive improvement**:

- classify the defect pattern
- update design guidelines and review checklists
- add new automated checks to catch similar issues earlier

### Tool Support for Counterexample Analysis

Modern model-checking tools provide dedicated support for analyzing
counterexamples.

**NuSMV trace facilities**:

【Context-dependent snippet】
```smv
show_traces -v
write_traces -o counterexample.xml
```

These commands display a counterexample trace and write it to a file.

**SPIN trace facilities**:

【Context-dependent snippet】
```bash
spin -t -p examples/ch08/spin/producer-consumer.pml
spin -t examples/ch08/spin/producer-consumer.pml
```

The first command prints a more detailed trail, and the second replays the
trace as a simulation.

**TLC trace facilities**:

- step-by-step display of states
- inspection of variable changes
- detailed presentation of the error state

### A Counterexample-Driven Development Process

Counterexamples can be integrated into the development process as recurring
engineering artifacts.

**Counterexample database**:

- systematic storage of discovered counterexamples
- classification and searchability
- traceability of repairs and their effects

**Regression checks**:

- confirm that the specific counterexample is gone
- check that no new defect was introduced
- evaluate performance impact of the repair

**Education and knowledge sharing**:

- share recurring defect patterns
- use representative traces for onboarding and training
- reuse them during design reviews

Counterexamples are among the most valuable outputs of model checking. Used
well, they improve both system quality and the engineering maturity of the
team.

## 8.6 Comparing Major Tools and Choosing Among Them

### The Ecosystem of Model-Checking Tools

As model checking has matured, a wide range of tools has emerged. Each tool is
specialized for certain problem classes or verification styles. Choosing the
right one has a substantial effect on the success of a verification effort.

### SPIN: A Pioneer in Concurrent-System Verification

SPIN, developed by Gerard Holzmann, remains one of the representative tools for
verifying concurrent systems.

**Main characteristics**:

- **Promela language** specialized for describing concurrent processes
- **partial order reduction** for controlling state explosion caused by
  interleavings
- **memory efficiency** for explicit-state exploration
- **random simulation** for lightweight pre-checks before full verification

**Example domain**:

【Context-dependent snippet】
```promela
mtype = { msg };
chan buffer = [1] of { mtype };

active proctype Producer() {
    do
    :: buffer!msg -> printf("Produced\n")
    od
}

active proctype Consumer() {
    do
    :: buffer?msg -> printf("Consumed\n")
    od
}
```

For a self-contained file, see `examples/ch08/spin/producer-consumer.pml`.

**Advantages**:

- natural description of concurrency
- highly optimized verification engine
- long industrial track record

**Constraints**:

- restricted data types compared with general-purpose languages
- nontrivial learning curve
- limited graphical tooling

### NuSMV: A Standard Tool for Symbolic Verification

NuSMV is a classic tool for symbolic model checking.

**Main characteristics**:

- **BDD-based representation** for large state sets
- **CTL and LTL support** for a wide range of temporal properties
- **hierarchical modules** for structured system descriptions
- **counterexample generation** for detailed diagnosis

**Specification example**:

【Context-dependent snippet】
```smv
MODULE main
VAR
    state : {idle, req, crit, exit};
    input_req : boolean;
    other_flag : boolean;

ASSIGN
    init(state) := idle;
    init(input_req) := FALSE;
    init(other_flag) := FALSE;
    next(input_req) := {TRUE, FALSE};
    next(other_flag) := {TRUE, FALSE};
    next(state) := case
        state = idle & input_req : req;
        state = req & !other_flag : crit;
        state = crit : exit;
        state = exit : idle;
        TRUE : state;
    esac;

LTLSPEC G(state = crit -> F(state = exit))
CTLSPEC AG(state = crit -> !other_flag)
```

For a self-contained file, see `examples/ch08/nusmv/request-response.smv`.

**Advantages**:

- declarative specification style
- strong symbolic engine
- broad academic and industrial use

**Constraints**:

- can be memory-intensive
- BDD construction may fail on some structures
- limited support for highly dynamic data structures

### TLC: The Execution Engine for TLA+

TLC is the model checker dedicated to TLA+ specifications.

**Main characteristics**:

- **high-level specification language** close to mathematics
- **set-theoretic values** such as sets, functions, and sequences, rather than a
  conventional static type system
- **explicit type invariants** commonly named `TypeOK` or `TypeInvariant`, which
  assert that variables belong to the expected sets
- **explicit-state exploration** of the reachable states of a concrete finite
  model
- **detailed configuration control** for constants, properties, state
  constraints, symmetry, and fairness

**TLA+ specification sketch**:

Pseudo notation:

```tla
Init ≜ balance = [a ∈ Accounts ↦ 0]

Transfer(from, to, amount) ≜
    ∧ balance[from] ≥ amount
    ∧ balance' = [balance EXCEPT
        ![from] = @ - amount,
        ![to] = @ + amount]

Next ≜ ∃ from, to ∈ Accounts, amount ∈ Nat :
    Transfer(from, to, amount)
```

**Advantages**:

- expressive specification language
- strong support for abstract modeling
- especially good for distributed protocols

**Constraints**:

- steep learning curve
- some distance from implementation code
- narrower toolchain than mainstream programming languages

### CBMC: A Practical Tool for Software Verification

CBMC is a bounded model checker for C and C++ programs.

**Main characteristics**:

- **direct verification of real code**
- **SAT-based reasoning** over bounded executions
- **concrete counterexample traces**
- **industrial use** in domains such as automotive and aerospace

**Verification example**:

【Context-dependent snippet】
```c
#include <assert.h>

extern int nondet_int(void);

int main(void) {
    int array[10];
    int index = nondet_int();

    __CPROVER_assume(index >= 0 && index < 10);
    array[index] = 42;

    int x = nondet_int();
    int y = nondet_int();
    __CPROVER_assume(x >= 0 && x <= 1000);
    __CPROVER_assume(y >= 0 && y <= 1000);

    int sum = x + y;
    __CPROVER_assert(sum >= x && sum >= y,
                     "sum grows for bounded non-negative inputs");
    return 0;
}
```

For a self-contained file, see `examples/ch08/cbmc/array-bounds.c`.

**Advantages**:

- works at implementation level
- reuses existing code assets
- produces concrete, actionable bug traces

**Constraints**:

- bounded verification only
- abstraction is still difficult for large programs
- performance can degrade on very large codebases

### SymbiYosys: Formal Verification of RTL {#rtl-formal-verification-symbiyosys}

The same transition-system view used in software model checking also applies to synchronous RTL.
SymbiYosys, whose CLI is `sby`, is a front end for an open-source formal flow centered on Yosys; it sends SystemVerilog RTL and formal properties to a backend solver.
The book's self-contained example checks a synchronous two-request arbiter for the safety property that both grants are never asserted together.

**Reading RTL as a transition system**

- **Clock**: one `always_ff @(posedge clk)` event is one step relating the current and next register values.
- **Reset**: the example assumes that `rst` is asserted for the first sampled edge and deasserted thereafter. It does not silently mix arbitrary unreset initial register values into the intended contract.
- **Finite bit vectors**: `logic` values and registers have fixed widths. When arithmetic is added, overflow, truncation, and signedness must be reviewed under the same fixed-width semantics as the property.
- **Cycle trace**: a counterexample or reachability witness records inputs, registers, and outputs by cycle in VCD form. `$past(req0)` means the value sampled at the preceding clock edge.

The three property constructs in this flow have different roles.

| Construct | Reading | Consequence of misuse |
| --- | --- | --- |
| `assert(P)` | Check that `P` is not violated on the executions under analysis | A weak property can omit the defect that matters |
| `assume(A)` | Restrict analyzed environment executions to those satisfying `A` | An over-strong assumption can remove a defective input trace |
| `cover(C)` | Search for at least one execution reaching `C` | Reachability does not prove safety or correctness of all executions |

**BMC, prove, and cover are different claims**

1. Running the flawed design in `mode bmc` at depth 6 finds, by step 3, a trace in which simultaneous requests lead to simultaneous grants in the following cycle. The expected `FAIL` is a successful teaching result and a bug found within six steps, not a general proof.
2. Running the fixed design in `mode prove` at depth 6 yields `PASS` for both the base case and temporal induction. This k-induction result is relative to the RTL, property, assumptions, Yosys transformation, and backend configuration.
3. Running the fixed design in `mode cover` reaches a witness in which simultaneous requests are followed by only the priority grant. This check complements the proof by showing that the interesting environment input was not excluded by an assumption.

The following files are the shared canonical assets. Retrieve the RTL, configuration, and expected result together from the same repository revision rather than copying only an excerpt or VCD.

- [examples/ch08/sby/rtl-arbiter/arbiter-flawed.sv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/arbiter-flawed.sv)
- [examples/ch08/sby/rtl-arbiter/arbiter-fixed.sv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/arbiter-fixed.sv)
- [examples/ch08/sby/rtl-arbiter/arbiter-flawed.sby](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/arbiter-flawed.sby)
- [examples/ch08/sby/rtl-arbiter/arbiter-fixed.sby](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/arbiter-fixed.sby)
- [examples/ch08/sby/rtl-arbiter/expected-flawed-bmc.json](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/expected-flawed-bmc.json)
- [examples/ch08/sby/rtl-arbiter/expected-fixed-prove.json](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/expected-fixed-prove.json)
- [examples/ch08/sby/rtl-arbiter/expected-fixed-cover.json](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/expected-fixed-cover.json)
- [examples/ch08/sby/rtl-arbiter/README.md](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/sby/rtl-arbiter/README.md)

<!-- example-contract: sby-rtl-arbiter-flawed-bmc -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id sby-rtl-arbiter-flawed-bmc
```

<!-- example-contract: sby-rtl-arbiter-fixed-prove -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id sby-rtl-arbiter-fixed-prove
```

<!-- example-contract: sby-rtl-arbiter-fixed-cover -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id sby-rtl-arbiter-fixed-cover
```

All three contracts run in the `nightly` lane and pin OSS CAD Suite 20260716, SBY `v0.67-4-gfea6e46`, Yosys `0.67+40`, Bitwuzla `0.9.1`, and depth 6.
Artifacts retain the mode, depth, timeout, tool/backend versions and commits, normalized result, and either the flawed counterexample VCD or the cover witness VCD; they do not contain the approximately 733 MB suite archive or its extracted binaries.

**Vacuity and over-constraint**

Adding `assume(!(req0 && req1))` could make the flawed design's mutual-exclusion assertion pass.
That change would not repair the arbiter; it would remove precisely the simultaneous-request behavior that the property is intended to examine.
Pairing the assertion with a meaningful cover, reviewing assumptions one by one, and refusing to treat an unreachable cover as success make this class of vacuity easier to detect.

> **Assurance boundary**: this contract covers the SystemVerilog formal subset accepted by Yosys, the stated clock/reset/environment assumptions, and the pinned property and solver configuration. It does not verify all of SystemVerilog Assertions, clock-domain crossings, timing closure, a post-synthesis netlist, physical or analog behavior, or a commercial EDA flow.

### Executable Example Contracts {#model-checker-executable-example-contracts}

The short SPIN, NuSMV, and CBMC fragments in this chapter are **context-dependent snippets**, even when their syntax matches the real tools, because execution still depends on launch options, generated artifacts, and surrounding model context. CI-backed executability is limited to the contract blocks below, which retrieve the shared JA/EN canonical assets from `examples/ch08/**` through the manifest runner.

Repository-wide, `pr-quick` and `nightly` are separated, and the contracts in this section stay on `nightly` to keep pull-request latency controlled. Normalized execution evidence is expected under `.artifacts/manifest/<id>/`, and readers should retrieve the canonical files from the same repository revision instead of copying the short inline fragments by themselves.

- `spin-ltl-properties`: canonical asset [examples/ch08/spin/ltl-properties.pml](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/spin/ltl-properties.pml); lane `nightly`; pinned version `SPIN 6.5.2`; expected success marker `errors: 0`. Retrieve [examples/ch08/spin/ltl-properties.pml](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/spin/ltl-properties.pml) from the same commit as the manuscript.
<!-- example-contract: spin-ltl-properties -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id spin-ltl-properties
```

- `spin-producer-consumer`: canonical asset [examples/ch08/spin/producer-consumer.pml](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/spin/producer-consumer.pml); lane `nightly`; pinned version `SPIN 6.5.2`; expected success marker `errors: 0`. Retrieve the self-contained Promela source from [examples/ch08/spin/producer-consumer.pml](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/spin/producer-consumer.pml) in the same revision.
<!-- example-contract: spin-producer-consumer -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id spin-producer-consumer
```

- `nusmv-fairness`: canonical asset [examples/ch08/nusmv/fairness.smv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/nusmv/fairness.smv); lane `nightly`; pinned version `NuSMV 2.7.1`; expected success marker `-- is true`. Retrieve the shared JA/EN asset from [examples/ch08/nusmv/fairness.smv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/nusmv/fairness.smv).
<!-- example-contract: nusmv-fairness -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id nusmv-fairness
```

- `nusmv-request-response`: canonical asset [examples/ch08/nusmv/request-response.smv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/nusmv/request-response.smv); lane `nightly`; pinned version `NuSMV 2.7.1`; expected result `-- is false`, representing the intentional counterexample while the NuSMV process itself exits successfully. Retrieve [examples/ch08/nusmv/request-response.smv](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/nusmv/request-response.smv) from the same repository revision.
<!-- example-contract: nusmv-request-response -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id nusmv-request-response
```

- `cbmc-array-bounds`: canonical asset [examples/ch08/cbmc/array-bounds.c](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/cbmc/array-bounds.c); lane `nightly`; pinned version `CBMC 6.10.0`; expected success marker `VERIFICATION SUCCESSFUL`. Retrieve the full source file from [examples/ch08/cbmc/array-bounds.c](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/ch08/cbmc/array-bounds.c) instead of copying the inline excerpt alone.
<!-- example-contract: cbmc-array-bounds -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id cbmc-array-bounds
```

### UPPAAL: Specialized for Real-Time Systems

UPPAAL is a tool specialized for real-time verification.

**Main characteristics**:

- **timed automata** as a natural model of timing constraints
- **graphical UI** for visual state-machine modeling
- **precise clock constraints**
- **optimization support** for fastest or lowest-cost paths

**Timed-automaton sketch**:

Pseudo notation:

```text
process Task {
    clock t;

    state Idle {
        when(trigger && t >= period) -> Running { t := 0; }
    }

    state Running {
        when(t <= deadline) -> Idle;
        when(t > deadline) -> Error; // deadline violation
    }
}
```

**Advantages**:

- precise reasoning about real-time behavior
- intuitive graphical descriptions
- useful for optimization questions as well as safety questions

**Constraints**:

- narrower applicability than general-purpose tools
- meaningful learning cost
- scale limits for very large systems

### Comparing Methods, Checked Scopes, and Results

The following categories describe search methods, not a hierarchy of assurance.
Either explicit-state or symbolic checking can provide strong evidence when it
completes over the stated model and property. Approximation, bounded analysis,
and incomplete runs narrow that evidence.

| Tool | Main method and state space | Scope that may be called exhaustive | Fairness and completion result | Main boundary |
| --- | --- | --- | --- | --- |
| SPIN | Explicit-state exploration of a Promela model | A finite model and selected properties when full-state search completes | Weak fairness is configuration-dependent; distinguish no violation, counterexample, and incomplete run | Bitstate hashing is approximate; state explosion and resource limits can remove exhaustiveness |
| TLC | Explicit-state exploration of a concrete finite TLA+ model | Reachable states under the `.cfg`, initial states, transitions, properties, and state constraints when the run completes | Liveness depends on WF/SF in the specification; distinguish no violation, counterexample, and incomplete run | Infinite reachable state spaces require finite modeling; abstraction, symmetry, and resources matter |
| NuSMV / nuXmv | Symbolic BDD-, SAT-, or SMT-based exploration | The model, logic, property, and fairness constraints handled by the selected engine when it completes | Timeout or `unknown` is not confirmation | Results depend on abstraction, finite- or infinite-state handling, engine, memory, and refinement success |
| CBMC | Bounded symbolic encoding of C/C++ executions | Executions within the unwind bound, input assumptions, and selected properties | No counterexample is a bound-relative result; solver `unknown` and timeout remain inconclusive | Executions beyond the bound are unchecked; environment models, undefined behavior, stubs, and solver behavior matter |

### Factors That Determine Tool Choice

The main criteria for choosing a model-checking tool are practical.

**1. Nature of the target system**:

- **concurrent systems** -> SPIN, TLC
- **hardware / embedded control** -> NuSMV, UPPAAL
- **software code** -> CBMC, Java PathFinder
- **real-time systems** -> UPPAAL, TIMES

**2. Required evidence and search contract**:

- **enumerate reachable states of a finite model** -> explicit-state tools such
  as SPIN and TLC
- **represent state sets symbolically** -> symbolic tools such as NuSMV / nuXmv
- **check real code to a stated bound** -> bounded model checkers such as CBMC
- **check liveness** -> a tool and logic for which the fairness assumptions can
  be recorded explicitly

**3. Technical background of the team**:

- **strong mathematical background** -> TLA+ / TLC
- **programming-oriented background** -> CBMC, Java PathFinder
- **modeling experience** -> NuSMV, UPPAAL

**4. Project constraints**:

- **learning time** -> shorter with CBMC, longer with TLA+
- **existing toolchain** -> integration matters
- **performance expectations** -> depend on target-system scale and complexity

### An Integrated Tool-Use Strategy

In practice, combinations of tools are often most effective.

**One possible staged verification strategy**:

1. **design stage**: choose TLA+, Promela, NuSMV, or another notation that fits
   the intended abstraction
2. **detailed design**: when moving a requirement to another model, record the
   correspondence and omitted behavior
3. **implementation stage**: use a tool such as CBMC to check code and its
   environment model to stated bounds
4. **integration stage**: connect model evidence to tests, monitoring, and
   implementation review

**Complementary verification**:

- **by property type**: confirm which safety and liveness properties each tool
  handles and under which fairness assumptions
- **by abstraction level**: connect high-level and implementation-level checks
  with refinement or a traceability table
- **by reasoning style**: compare evidence by completion criteria and unchecked
  scope, not by ranking symbolic above explicit-state exploration

### Emerging Tools and Trends

As verification technology evolves, new tools and frameworks continue to
appear:

- **CATAPULT** for high-level synthesis verification
- **SEAHORN** as an LLVM-based verification framework
- **SMACK** for translating LLVM into Boogie-based workflows
- **KLEE** as a symbolic-execution engine

The border between model checking, symbolic execution, theorem proving, and
static analysis is increasingly fluid.

### Practical Adoption Guidelines

**Evaluation phase**:

1. try the tool on a small example
2. evaluate learning cost and expected benefit
3. check compatibility with the existing development process

**Introduction phase**:

1. run a pilot project
2. share knowledge within the team
3. expand the scope gradually

**Institutionalization phase**:

1. update tools regularly
2. accumulate reusable verification patterns
3. transfer the lessons to other projects

The right tool choice has decisive influence on the success of model checking.
Technical features matter, but so do team capability, project constraints, and
long-term strategy.

---

## End-of-Chapter Exercises

**If you use AI while working through these exercises**

- Treat AI output as a proposal; use verifiers to make the final judgment.
- Keep a record of the prompts you used, the generated specifications and
  invariants, the verification commands and logs (including seed, depth, and
  scope), and the revision history when counterexamples were found.
- For detailed templates, see Appendix D and Appendix F.

### Basic Exercise 1: Practicing Temporal Logic

Describe properties of the following system in both CTL and LTL.

**Elevator control system**:

- states: `{idle, moving_up, moving_down, door_open}`
- events: `{call_button, arrive_floor, open_door, close_door}`

Properties to write:

1. **Safety**: the elevator never moves while the door is open
2. **Liveness**: if a call arrives, the elevator eventually arrives
3. **Fairness**: every floor is served fairly
4. **Efficiency**: no unnecessary movement occurs

For each property:

- write a CTL formula
- write an LTL formula
- explain which logic expresses it more naturally

### Basic Exercise 2: State-Space Analysis

Analyze the state space of the following concurrent system.

**Shared-counter system with two processes**:

Pseudo notation:

```text
Process 1:
  loop: read counter -> increment -> write counter

Process 2:
  loop: read counter -> decrement -> write counter
```

Items to analyze:

1. calculate the number of possible states when the counter ranges from 0 to
   10
2. draw the state-transition graph
3. identify race conditions
4. determine whether deadlock states exist
5. discuss whether partial order reduction applies

### Practical Exercise 1: Verification with SPIN

Describe the readers-writers problem in Promela and verify it with SPIN.

**Requirements**:

- multiple readers may read simultaneously
- a writer must write exclusively
- readers and writers must not access the resource at the same time
- starvation must be avoided

**Implementation elements**:

1. process definitions in Promela
2. description of shared data structures
3. implementation of synchronization primitives
4. description of safety and liveness properties
5. verification with SPIN and analysis of the results

### Practical Exercise 2: Verification with NuSMV

Describe a traffic-light control system in NuSMV and verify it.

**System specification**:

- north-south and east-west signals
- three states per direction: red, yellow, and green
- vehicle-detection sensors
- pedestrian push buttons

**Verification items**:

1. **Safety**: conflicting directions never become green at the same time
2. **Liveness**: every direction eventually gets green
3. **Responsiveness**: pedestrian requests are handled appropriately
4. **Efficiency**: unnecessary signal changes are avoided

### Advanced Exercise: Staged Verification with Multiple Tools

Design a consensus algorithm for a distributed database and verify it
progressively with multiple tools.

**System requirements**:

- three database nodes
- a majority-based agreement mechanism
- tolerance of node failures
- guaranteed data consistency

**Staged verification process**:

**Phase 1: High-level design in TLA+**

1. describe the overall algorithm in TLA+
2. verify the basic safety and liveness properties
3. perform an initial check with TLC

**Phase 2: Refinement in Promela**

1. refine the message-exchange protocol
2. describe concurrency and communication in more detail
3. verify the model with SPIN

**Phase 3: Implementation-level verification**

1. implement the actual C or Java code
2. verify it with CBMC or Java PathFinder
3. integrate the results with unit tests

**Integrated analysis**:

- classify the problems found at each stage
- compare the consistency of results across tools
- analyze the relationship between abstraction level and defect discovery
- evaluate the overall verification strategy

**Evaluation points**:

1. understanding the features and suitable use cases of each tool
2. understanding the quality impact of staged verification
3. understanding the trade-off between learning cost and verification benefit
4. evaluating applicability to real projects

Through these exercises, you should acquire both a theoretical understanding
of model checking and the practical ability to apply it. The advanced exercise
is especially important because it exposes you to the complexity of real
projects and to the need for a systematic verification strategy.
