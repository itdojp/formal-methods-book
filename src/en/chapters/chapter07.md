# Chapter 7: Specifying Time: Introduction to TLA+

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter07.md`

## 7.1 The Challenge of Distributed Systems: Time and State Become Complex

### The Fundamental Difficulty of Distribution

Distributed systems are one of the key technical foundations of modern digital
society, but their design and implementation involve difficulties that are
qualitatively different from those of a single-machine system. Those
difficulties arise because physical constraints and logical constraints interact
in complicated ways.

The most fundamental problem is the ambiguity of time. In a single machine, the
execution order of instructions is largely deterministic, so the statement "A
executed before B" has a clear meaning. In a distributed system, however, the
temporal order between operations running on different machines is not obvious.

### The Limits of Physical Time

Each machine has its own local clock, and perfect synchronization among those
clocks is impossible. Relativity already tells us that absolute simultaneity is
not a physically meaningful concept. Even at a practical engineering level,
network delay, clock skew, and timezone differences make it hard to share one
precise notion of time.

Suppose two servers, one in Tokyo and one in New York, each execute an
operation at "12:00:00.000" according to their own clocks. Were those actions
truly simultaneous? Once we account for timezone offsets, network delay, and
clock precision, the answer becomes uncertain.

### Increasing Complexity of Causality

In a distributed system, causal relationships among events become more subtle.
For event A to be the cause of event B, information about A must have reached
B. Because information propagation takes time, physical timestamps alone are not
enough.

【Pseudo notation】
```text
Node 1: event A occurs → send message
         |
         ↓ (network delay)
Node 2: receive message → event B occurs
```

To reason about such situations, we need a notion of logical time, not just
physical time.

### The Reality of Partial Failure

Partial failure is unavoidable in distributed systems. One part of the system
may fail while the rest continues to operate. This is very different from the
usual failure mode of a single-machine program.

Typical examples of partial failure include the following.

- **Network partition**: communication between some nodes is lost.
- **Node failure**: a particular machine stops responding.
- **Performance degradation**: one part of the system becomes much slower.
- **Byzantine failure**: a node behaves arbitrarily or maliciously.

Maintaining consistency under such conditions is one of the core design
problems of distributed systems.

### The Trade-Off Between Consistency and Availability

One of the most important findings in distributed-systems theory is the CAP
theorem. It says that the following three properties cannot all be guaranteed
at the same time.

- **Consistency**: all nodes observe the same data.
- **Availability**: the system always returns a response.
- **Partition tolerance**: the system continues to operate despite network
  partitions.

In practice, partitions cannot be ruled out, so a system must make design
choices that trade consistency against availability depending on its needs.

### Managing Nondeterminism

Nondeterminism is an essential feature of distributed systems. Even from the
same initial state, different network delays or scheduling decisions may lead
to different outcomes.

That nondeterminism gives flexibility, but it also makes correctness harder to
guarantee. We need to ensure that the system remains safe under *all* relevant
execution orders, not just a convenient one.

### The Difficulty of Consensus

Distributed systems repeatedly face the need for agreement. Multiple nodes must
agree on a value, a leader, or an ordering of operations. That turns out to be
harder than it first appears.

The FLP impossibility result shows that in an asynchronous distributed system,
if even a single node can fail, there is no deterministic consensus algorithm
that always guarantees termination. This theoretical limit is one of the key
reasons why practical systems rely on additional assumptions such as timing
bounds, failure restrictions, or probabilistic techniques.

### State Explosion

The state space of a distributed system grows exponentially with the number of
nodes. If each of `N` nodes has `K` possible local states, then the combined
system may have `K^N` global states.

This state explosion makes it hard to understand all possible behaviors by
informal reasoning alone. Formal methods are therefore essential for controlling
complexity and guaranteeing critical properties.

### TLA+ as an Approach to These Problems

TLA+ (Temporal Logic of Actions) addresses these difficulties through a few key
ideas.

- **Temporal logic for dynamic properties**: properties such as "always" and
  "eventually" can be written precisely.
- **State-transition modeling**: a system is abstracted as states and the
  transitions among them.
- **Actions as structured change**: state change is described explicitly as an
  action.
- **Fairness assumptions for realistic modeling**: the specification can rule
  out unrealistic executions caused only by pathological scheduling.

TLA+ does not make the essential difficulties of distributed systems disappear.
Instead, it makes them explicit and therefore analyzable.

## 7.2 The Philosophy of TLA+: Actions and Temporal Logic

### Leslie Lamport's Central Insight

One of Leslie Lamport's most important insights was that system behavior can be
understood as a sequence of states. That idea seems simple, but it has major
consequences.

Traditional programming often focuses on the execution of commands. Lamport's
view shifts attention from "which instruction ran" to "how the system state
changed." Once that viewpoint is adopted, even complicated distributed behavior
can be understood in a uniform way.

### A Worldview Based on State-Transition Systems

In TLA+, every system is treated as a state-transition system. The system starts
from an initial state and evolves through a sequence of transitions.

【Pseudo notation】
```text
initial state → state 1 → state 2 → state 3 → ...
```

The state contains every relevant piece of information about the system: the
values of program variables, the status of the network, the local state of each
node, and any other information that can influence behavior.

### Actions as Abstractions of Change

In TLA+, an *action* describes a relationship between a current state and a
next state. Formally, an action is a predicate over unprimed and primed
variables.

For example, an action that increments `x` can be written as follows.

【Pseudo notation】
```tla
Increment ≜ x' = x + 1
```

Here `x` denotes the value in the current state and `x'` denotes the value in
the next state.

### The Expressive Power of Temporal Logic

TLA+ uses temporal logic to express dynamic properties of behavior.

**`□` (always)**:

【Pseudo notation】
```tla
□(x ≥ 0)
```

This says that `x` is always non-negative.

**`◇` (eventually)**:

【Pseudo notation】
```tla
◇(x = 10)
```

This says that `x` becomes 10 at some point.

**`○` (next)** is common in temporal-logic explanation, although ordinary TLA+
specifications usually work directly with primed variables and action formulas
rather than with a separate next-time operator.

【Pseudo notation】
```tla
○(x > y)
```

These operators can be combined to describe richer behavior.

【Pseudo notation】
```tla
□◇(process = "ready")
◇□(system = "stable")
```

The first says that the process becomes ready infinitely often. The second says
that the system eventually reaches a stable condition and stays there.

### The Power of Prime Notation

Prime notation is one of the cleanest ideas in TLA+. It distinguishes the
current state from the next state concisely and directly.

【Pseudo notation】
```tla
Transfer ≜
  ∧ amount > 0
  ∧ balance_from ≥ amount
  ∧ balance_from' = balance_from - amount
  ∧ balance_to' = balance_to + amount
```

This reads naturally as a state change: the amount is positive, the source
account has enough funds, and then the two balances are updated accordingly.

### The Meaning of Fairness

In a concurrent or distributed system, an action may be enabled forever in the
specification and yet never be scheduled in some pathological execution.
Fairness is a way to rule out such unrealistic behaviors by assumption. It does
*not* mean that an implementation automatically becomes fair merely because the
specification includes fairness.

Here `ENABLED A` means that from the current state, some next state exists that
satisfies action `A`.

- **Weak fairness (`WF`)**: if an action is continuously enabled from some
  point onward, then it must eventually occur.
- **Strong fairness (`SF`)**: if an action becomes enabled infinitely often,
  then it must eventually occur.

【Tool-compliant (runs as-is)】
```tla
WF_vars(Action)
SF_vars(Action)
```

### Compositionality

TLA+ supports compositionality. Larger systems can be built from smaller
specifications.

【Pseudo notation】
```tla
System ≜ Process1 ∧ Process2 ∧ Process3
```

Each process can be specified independently, then combined using logical
conjunction.

### Stepwise Refinement

TLA+ also supports refinement: a concrete specification can be shown to realize
an abstract one. This allows development to proceed from a high-level design to
an implementable model while preserving important guarantees.

【Pseudo notation】
```text
abstract specification ⊨ concrete specification
```

The notation above is explanatory rather than executable TLA+ code, but it
captures the refinement idea.

### Accepting Nondeterminism

TLA+ does not treat nondeterminism as a flaw to be eliminated. Instead, it is a
valuable modeling tool. By allowing different actions to be chosen
nondeterministically, the specification can preserve implementation freedom
while still enforcing the required safety properties.

【Pseudo notation】
```tla
Next ≜ Action1 ∨ Action2 ∨ Action3
```

The specification does not force one branch to be chosen. Instead, it requires
all possible choices to be safe.

### Putting Mathematical Foundations to Work

TLA+ is built on set theory, logic, and computation theory, but it integrates
those foundations into a notation designed for system engineering. Because it
can work naturally with sets, functions, sequences, and quantified formulas, it
scales from abstract models to detailed protocol behavior.

### Integration with Tools

TLA+ is not just a description language. It is tightly integrated with tooling,
most notably TLC, the TLA+ model checker. That integration is one of its most
important practical strengths: a mathematically written specification can be
checked automatically against concrete finite models.

## 7.3 State and Action: The Dynamic Model of a System

### Structuring the State Space

In TLA+, a state represents the complete relevant information about the system.
This may include program variables, network state, local node state, and any
other information that affects behavior.

A state can often be understood as a function from variables to values. For
example, a banking system might be modeled as follows.

【Pseudo notation】
```tla
State ≜ [
  accounts: [AccountID → Nat],
  transactions: Seq(Transaction),
  current_time: Time,
  network_status: NetworkState
]
```

This gives a compact description of the full situation at one moment.

### Defining Variables and Types

TLA+ makes the state variables explicit, and type-like invariants can restrict
them to the values that make sense for the model.

【Pseudo notation】
```tla
VARIABLES
  balance,
  pending,
  log,
  clock

TypeInvariant ≜
  ∧ balance ∈ [AccountID → Nat]
  ∧ pending ∈ SUBSET Transaction
  ∧ log ∈ Seq(LogEntry)
  ∧ clock ∈ Nat
```

Although TLA+ itself is untyped, such invariants play the role of a type
discipline for the model.

### Specifying the Initial State

Behavior begins from `Init`, the predicate describing the initial state.

【Pseudo notation】
```tla
Init ≜
  ∧ balance = [a ∈ AccountID ↦ InitialBalance[a]]
  ∧ pending = {}
  ∧ log = ⟨⟩
  ∧ clock = 0
```

The initial state fixes what is true at the start of every behavior.

### State Change Through Actions

An action describes one way the state can evolve.

**Deposit example**:

【Pseudo notation】
```tla
Deposit(account, amount) ≜
  ∧ amount > 0
  ∧ account ∈ DOMAIN balance
  ∧ balance' = [balance EXCEPT ![account] = @ + amount]
  ∧ log' = Append(log, [type ↦ "deposit", account ↦ account, amount ↦ amount])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

This says that a deposit increases the selected balance, appends a log entry,
and advances the clock, while leaving `pending` unchanged.

### The Complexity of a Transfer Operation

Transfers are more complex because several parts of the state must be updated
consistently.

【Pseudo notation】
```tla
Transfer(from, to, amount) ≜
  ∧ amount > 0
  ∧ from ≠ to
  ∧ from ∈ DOMAIN balance ∧ to ∈ DOMAIN balance
  ∧ balance[from] ≥ amount
  ∧ balance' = [balance EXCEPT
      ![from] = @ - amount,
      ![to] = @ + amount]
  ∧ log' = Append(log, [type ↦ "transfer", from ↦ from, to ↦ to, amount ↦ amount])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

### Conditional Actions

Many actions are meaningful only under certain conditions.

【Pseudo notation】
```tla
ProcessPendingTransaction ≜
  ∧ pending ≠ {}
  ∧ ∃ t ∈ pending :
      ∧ CanProcess(t)
      ∧ ExecuteTransaction(t)
      ∧ pending' = pending \ {t}
  ∧ UNCHANGED ⟨balance, log, clock⟩
```

### Nondeterministic Choice

A TLA+ next-state relation often combines many possible actions.

【Pseudo notation】
```tla
Next ≜
  ∨ ∃ account ∈ AccountID, amount ∈ Nat : Deposit(account, amount)
  ∨ ∃ from, to ∈ AccountID, amount ∈ Nat : Transfer(from, to, amount)
  ∨ ProcessPendingTransaction
  ∨ TimeoutCleanup
```

The system may take any of these actions, provided the chosen action's
constraints are satisfied.

### The Importance of Frame Conditions

When an action is written, it is important to make clear which variables do
*not* change. These frame conditions prevent unintended side effects.

【Pseudo notation】
```tla
ReadBalance(account) ≜
  ∧ account ∈ DOMAIN balance
  ∧ UNCHANGED ⟨balance, pending, log, clock⟩
```

A read-only action should explicitly state that all relevant variables remain
unchanged.

### Expressing Atomicity

When several changes must happen together, they are written in one action.
This is how atomicity is expressed.

【Pseudo notation】
```tla
AtomicSwap(account1, account2) ≜
  ∧ account1 ≠ account2
  ∧ account1 ∈ DOMAIN balance ∧ account2 ∈ DOMAIN balance
  ∧ balance' = [balance EXCEPT
      ![account1] = balance[account2],
      ![account2] = balance[account1]]
  ∧ log' = Append(log, [type ↦ "swap", acc1 ↦ account1, acc2 ↦ account2])
  ∧ clock' = clock + 1
  ∧ UNCHANGED pending
```

### Modeling the Passage of Time

Some systems require explicit representation of time passing.

【Pseudo notation】
```tla
TickClock ≜
  ∧ clock' = clock + 1
  ∧ ProcessTimeouts
  ∧ UNCHANGED ⟨balance, pending⟩

ProcessTimeouts ≜
  log' = [i ∈ DOMAIN log ↦
    IF log[i].timestamp + TIMEOUT ≤ clock'
    THEN [log[i] EXCEPT !.status = "expired"]
    ELSE log[i]]
```

### Interacting with the Environment

A system usually interacts with clients, users, or other external components.
That interaction can also be modeled as actions.

【Pseudo notation】
```tla
ReceiveExternalRequest(request) ≜
  ∧ ValidRequest(request)
  ∧ pending' = pending ∪ {request}
  ∧ log' = Append(log, [type ↦ "request_received", request ↦ request])
  ∧ clock' = clock + 1
  ∧ UNCHANGED balance
```

### Modeling Failures

Practical models often need explicit failure actions.

【Pseudo notation】
```tla
NetworkFailure ≜
  ∧ network_status = "operational"
  ∧ network_status' = "failed"
  ∧ pending' = {}
  ∧ UNCHANGED ⟨balance, log, clock⟩

Recovery ≜
  ∧ network_status = "failed"
  ∧ network_status' = "operational"
  ∧ UNCHANGED ⟨balance, pending, log, clock⟩
```

### Constraints as State Predicates

Desired properties can also be written as state predicates and invariants.

【Pseudo notation】
```tla
SafetyInvariant ≜
  ∧ TypeInvariant
  ∧ ∀ a ∈ DOMAIN balance : balance[a] ≥ 0
  ∧ TotalMoney' = TotalMoney

TotalMoney ≜ Sum({balance[a] : a ∈ DOMAIN balance})
```

This kind of formula captures the consistency properties that every reachable
state or transition should respect.

## 7.4 Temporal Logic: A Language for "When" and "How"

### Abstracting Time

Temporal logic is a logical system for reasoning about time. In TLA+, time is
abstracted as a sequence of states rather than treated primarily as physical
clock time. This makes it possible to describe essential temporal properties
without relying on one concrete timestamping scheme.

The power of temporal logic lies in its focus on order and inevitability rather
than on precise wall-clock values.

### Basic Temporal Operators

TLA+ uses several foundational temporal operators.

**`□` (always)**:

【Pseudo notation】
```tla
□P
```

Example:

【Pseudo notation】
```tla
□(balance ≥ 0)
□(mutex ⟹ ¬(process1_critical ∧ process2_critical))
```

**`◇` (eventually)**:

【Pseudo notation】
```tla
◇P
```

Example:

【Pseudo notation】
```tla
◇(task_completed)
◇(system_stable)
```

### Combining Operators

Temporal operators can be combined to express richer long-run behavior.

**`□◇P`**: `P` holds infinitely often.

【Pseudo notation】
```tla
□◇(process_scheduled)
□◇(garbage_collection)
```

**`◇□P`**: eventually `P` becomes permanently true.

【Pseudo notation】
```tla
◇□(leader_elected)
◇□(consensus_reached)
```

### The Leads-To Relation

A very common temporal idea is that whenever `A` happens, `B` eventually
follows.

【Pseudo notation】
```tla
A ~> B ≜ □(A ⟹ ◇B)
```

Example:

【Pseudo notation】
```tla
request_sent ~> response_received
failure_detected ~> recovery_initiated
```

### Distinguishing Safety from Liveness

Temporal properties are often divided into two main categories.

**Safety**: nothing bad ever happens.

【Pseudo notation】
```tla
Safety ≜ □¬BadThing
```

Examples:

【Pseudo notation】
```tla
□¬(balance < 0)
□¬(deadlock)
```

**Liveness**: something good eventually happens.

【Pseudo notation】
```tla
Liveness ≜ ◇GoodThing
```

Examples:

【Pseudo notation】
```tla
◇(all_processes_terminate)
□(request ⟹ ◇response)
```

### Temporal Expressions of Fairness

Fairness can also be written precisely in temporal form.

**Weak fairness**:

【Pseudo notation】
```tla
WF_vars(A) ≜ ◇□ENABLED ⟨A⟩_vars ⟹ □◇⟨A⟩_vars
```

This says that if action `A` eventually remains enabled forever, then it must
occur infinitely often.

**Strong fairness**:

【Pseudo notation】
```tla
SF_vars(A) ≜ □◇ENABLED ⟨A⟩_vars ⟹ □◇⟨A⟩_vars
```

This says that if `A` becomes enabled infinitely often, then it must also occur
infinitely often.

Note that `⟨A⟩_vars` excludes stuttering by requiring that action `A` occurs and
that the tuple `vars` actually changes.

### Temporal Properties of Mutual Exclusion

Mutual exclusion is a standard example of temporal reasoning.

【Pseudo notation】
```tla
MutualExclusion ≜
  ∀ i, j ∈ Processes : i ≠ j ⟹ □¬(pc[i] = "critical" ∧ pc[j] = "critical")

Starvation_Free ≜
  ∀ i ∈ Processes : (pc[i] = "trying") ~> (pc[i] = "critical")

Progress ≜
  (∃ i ∈ Processes : pc[i] = "trying") ⟹ ◇(∃ j ∈ Processes : pc[j] = "critical")
```

### Temporal Properties of Distributed Consensus

Consensus algorithms require several classic temporal properties.

**Agreement**:

【Pseudo notation】
```tla
Agreement ≜
  ∀ p, q ∈ Nodes :
    (decided[p] ∧ decided[q]) ⟹ (decision[p] = decision[q])
```

**Validity**:

【Pseudo notation】
```tla
Validity ≜
  ∀ p ∈ Nodes :
    decided[p] ⟹ decision[p] ∈ {proposed[q] : q ∈ Nodes}
```

**Termination**:

【Pseudo notation】
```tla
Termination ≜
  ◇(∀ p ∈ Nodes : decided[p])
```

### Temporal Expressions of Causality

Distributed systems also require temporal reasoning about causal dependence.

【Pseudo notation】
```tla
CausalOrder ≜
  ∀ e1, e2 ∈ Events :
    (e1.timestamp < e2.timestamp ∧ e1.node = e2.node) ⟹
    (e1 happens_before e2)

EventualConsistency ≜
  ◇□(∀ n1, n2 ∈ Nodes : replica[n1] = replica[n2])
```

### Expressing Time Bounds

Practical systems often require bounded-response guarantees.

【Pseudo notation】
```tla
ResponseTime ≜
  ∀ req ∈ Requests :
    (request_sent(req)) ~> (response_received(req) ∧ time ≤ req.timestamp + TIMEOUT)

PeriodicMaintenance ≜
  □◇(maintenance_performed ∧ time_since_last_maintenance ≤ MAINTENANCE_INTERVAL)
```

Some of these formulas are explanatory and use notation that is not standard
raw TLA+ syntax. They should therefore be read as pseudo notation.

### Temporal Models of Failure and Recovery

Failures and recoveries are also naturally expressed as temporal requirements.

【Pseudo notation】
```tla
FailureRecovery ≜
  □(failure_detected ~> recovery_initiated)

Availability ≜
  □◇(system_operational)

BoundedDowntime ≜
  □(failure_occurred ⟹ ◇≤MAX_DOWNTIME system_operational)
```

### More Complex Temporal Properties

Real systems usually require several temporal concerns to be combined.

【Pseudo notation】
```tla
SystemSpec ≜
  ∧ Safety_Properties
  ∧ Liveness_Properties
  ∧ Fairness_Assumptions

Safety_Properties ≜
  ∧ MutualExclusion
  ∧ DataConsistency
  ∧ SecurityPolicy

Liveness_Properties ≜
  ∧ Progress
  ∧ EventualTermination
  ∧ ServiceAvailability

Fairness_Assumptions ≜
  ∧ ∀ i ∈ Processes : WF_vars(Step(i))
  ∧ ∀ msg ∈ Messages : SF_vars(Deliver(msg))
```

### The Power and Limits of Temporal Logic

Temporal logic is powerful, but not omnipotent.

**It expresses well**:

- safety and liveness;
- fairness and progress;
- causal and ordering constraints; and
- recurring or eventual patterns of behavior.

**Its limits include**:

- quantitative real-time reasoning in full generality;
- probabilistic guarantees;
- explicit resource-consumption analysis; and
- highly detailed numeric optimization.

The key is to choose an abstraction level at which the temporal properties are
both meaningful and analyzable.

## 7.5 Practical Model Checking with TLC

### What TLC Is

TLC (the TLA+ model checker) is the principal analysis tool for executable TLA+
specifications. Developed around Leslie Lamport's work, it explores behaviors
of a finite model automatically and checks whether desired properties hold.

The main value of TLC is that it makes mathematical specifications operational.
Problems that are hard to spot from formulas alone often appear immediately as
concrete counterexamples.

### The Basic Principle of Model Checking

Model checking systematically explores the state space of the system and asks
whether any reachable state or behavior violates the properties of interest.
TLC follows a pattern such as this:

1. generate all states satisfying `Init`;
2. compute successors using `Next`;
3. check invariants and temporal properties on the reachable states and
   behaviors; and
4. report a counterexample trace if a violation is found.

### Executability of a Specification

For TLC to analyze a specification, the model must be executable in a finite
sense. That means restricting an abstract specification to finite sets and
finite bounds that TLC can enumerate.

【Pseudo notation】
```tla
CONSTANTS
  Processes,
  MaxBalance,
  MaxTime

ASSUME
  ∧ Processes ⊆ {"p1", "p2", "p3"}
  ∧ MaxBalance ∈ Nat ∧ MaxBalance ≤ 1000
  ∧ MaxTime ∈ Nat ∧ MaxTime ≤ 100
```

### Creating a Configuration File

TLC is controlled through a configuration file (`.cfg`) that supplies concrete
constant values, the specification to check, and the properties to verify.

【Pseudo notation】
```text
\* BankingSystem.cfg
CONSTANTS
  Accounts = {"A1", "A2", "A3"}
  InitialBalance = 100

SPECIFICATION Spec

INVARIANTS
  TypeInvariant
  SafetyInvariant

PROPERTIES
  ProgressProperty
  LivenessProperty
```

### A Stepwise Verification Strategy

A staged approach is effective for nontrivial systems.

**Stage 1: type-style invariants**

【Pseudo notation】
```tla
TypeInvariant ≜
  ∧ balance ∈ [Accounts → Nat]
  ∧ pending ∈ SUBSET Transactions
  ∧ clock ∈ Nat
```

**Stage 2: safety invariants**

【Pseudo notation】
```tla
SafetyInvariant ≜
  ∧ ∀ a ∈ Accounts : balance[a] ≤ MaxBalance
  ∧ ∀ t ∈ pending : t.amount > 0
  ∧ TotalMoney = CHOOSE n ∈ Nat : TRUE
```

**Stage 3: liveness properties**

【Pseudo notation】
```tla
Progress ≜ □(pending ≠ {} ⟹ ◇(pending = {}))
```

### Controlling the State Space

TLC's usefulness depends heavily on the size of the explored state space. Good
control techniques therefore matter.

**Using symmetry**:

【Tool-compliant (runs as-is)】
```tla
SYMMETRY Permutations(Accounts)
```

This is typically used in a model or configuration context to reduce the number
of symmetric states that TLC explores.

**Adding state constraints**:

【Pseudo notation】
```tla
StateConstraint ≜
  ∧ clock ≤ MaxTime
  ∧ ∀ a ∈ Accounts : balance[a] ≤ MaxBalance
  ∧ Cardinality(pending) ≤ MaxPendingTransactions
```

### Analyzing Error Traces

When TLC finds a violation, it reports the execution trace that leads to it.
Analyzing that trace is often the fastest route to understanding the root
cause.

**Typical output example**:

【Pseudo notation】
```text
Error: Invariant SafetyInvariant is violated.

State 1: (Initial state)
balance = (A1 :> 100 @@ A2 :> 100 @@ A3 :> 100)
pending = {}
clock = 0

State 2:
balance = (A1 :> 50 @@ A2 :> 100 @@ A3 :> 100)
pending = {[from |-> "A1", to |-> "A2", amount |-> 50]}
clock = 1

State 3:
balance = (A1 :> 50 @@ A2 :> 150 @@ A3 :> 100)
pending = {}
clock = 2
```

### Detecting Deadlock

TLC can automatically report deadlock when the system reaches a state in which
no enabled transition exists.

【Pseudo notation】
```tla
BadMutex ≜
  ∧ pc[1] = "wait" ∧ pc[2] = "wait"
  ∧ ∀ i ∈ {1,2} : UNCHANGED pc[i]

\* TLC may report:
\* Error: Deadlock reached.
```

### Verifying Liveness Properties

Checking liveness is generally more expensive than checking safety. TLC uses
specialized graph analysis techniques, such as strongly connected components,
to search for liveness violations.

【Pseudo notation】
```tla
EventualProgress ≜
  ∀ i ∈ Processes : □(pc[i] = "trying" ⟹ ◇(pc[i] = "critical"))
```

A TLC violation report for such a property will typically show a cycle in which
a desired event is postponed forever.

### Probabilistic or Sampling-Based Checking

For very large state spaces, exhaustive checking may be impractical. In such
cases, bounded or sampling-oriented approaches may be used operationally, even
though their guarantees differ from exhaustive model checking.

【Pseudo notation】
```text
CONSTRAINT StateConstraint
SYMMETRY Symmetries
CHECK_DEADLOCK TRUE
COVERAGE 80
```

### Performance-Optimization Techniques

Several practical techniques improve TLC performance.

**Parallel execution**:

【Tool-compliant (runs as-is)】
```bash
tlc -workers 8 BankingSystem.tla
```

**Memory tuning**:

【Tool-compliant (runs as-is)】
```bash
tlc -Xmx8g -XX:+UseG1GC BankingSystem.tla
```

**Checkpointing**:

【Tool-compliant (runs as-is)】
```bash
tlc -checkpoint 60 BankingSystem.tla
```

### Iterative Specification Improvement

In practice, TLC is usually used in an iterative loop.

1. write an initial specification;
2. run TLC;
3. analyze the error or counterexample;
4. improve the specification; and
5. run TLC again.

This cycle gradually improves both the model and the team's understanding of
the system.

### Practical Verification Strategy

Useful practical tactics include the following.

- **Start small**: begin with the smallest model that can express the core
  problem.
- **Expand gradually**: add more detail step by step.
- **Check continuously**: rerun verification when the specification changes.
- **Monitor performance**: record runtime and state counts to detect scaling
  issues early.

### Understanding the Limits of TLC

TLC also has clear limitations.

- **State explosion**: the state space can grow exponentially.
- **Need for finite models**: infinite sets cannot be handled directly.
- **Time cost**: large models may take a long time to check.
- **Memory cost**: the number of states is limited by available memory.

Practical use of TLC depends on extracting the maximum value within those
constraints.

## 7.6 Applying TLA+ to the Real World: A Distributed Consensus Algorithm

### The Essence of the Distributed Consensus Problem

Distributed consensus is one of the most fundamental problems in distributed
systems. Multiple nodes must agree on a value or decision despite failures,
message delay, and uncertainty about the state of the rest of the system.

The challenge is not only to reach agreement, but to do so in a way that keeps
the decision stable once made.

### A Formal Definition of Consensus

A distributed consensus algorithm is expected to satisfy three standard
properties.

- **Agreement**: any nodes that decide must decide the same value.
- **Validity**: the chosen value must have been proposed by some node.
- **Termination**: all non-faulty nodes eventually decide.

In TLA+, we can express them as follows.

【Pseudo notation】
```tla
VARIABLES
  proposed,
  decided,
  decision,
  phase

Agreement ≜
  ∀ p, q ∈ Nodes :
    (decided[p] ∧ decided[q]) ⟹ (decision[p] = decision[q])

Validity ≜
  ∀ p ∈ Nodes :
    decided[p] ⟹ decision[p] ∈ {proposed[q] : q ∈ Nodes}

Termination ≜
  ◇(∀ p ∈ Nodes : decided[p])
```

### Overview of Raft

Raft is a distributed consensus algorithm designed with understandability in
mind. It separates the problem into leader election and log replication, which
makes the design easier to reason about.

Its central concepts include:

- **roles**: `Leader`, `Follower`, and `Candidate`;
- **terms**: monotonically increasing epochs of leadership; and
- **log entries**: the ordered operations that the cluster agrees on.

### The State Model of Raft

A TLA+ model of Raft can make all of these pieces explicit.

【Tool-compliant (runs as-is)】
```tla
VARIABLES
  \* Persistent state on all servers
  currentTerm,
  votedFor,
  log,

  \* Volatile state on all servers
  state,
  commitIndex,

  \* Volatile state on leaders
  nextIndex,
  matchIndex,

  \* Auxiliary state
  messages,
  election_timer,
  heartbeat_timer
```

### Defining the Initial State

Initially, all servers begin as followers.

【Pseudo notation】
```tla
Init ≜
  ∧ currentTerm = [s ∈ Servers ↦ 0]
  ∧ votedFor = [s ∈ Servers ↦ Nil]
  ∧ log = [s ∈ Servers ↦ ⟨⟩]
  ∧ state = [s ∈ Servers ↦ Follower]
  ∧ commitIndex = [s ∈ Servers ↦ 0]
  ∧ nextIndex = [s ∈ Servers ↦ [t ∈ Servers ↦ 1]]
  ∧ matchIndex = [s ∈ Servers ↦ [t ∈ Servers ↦ 0]]
  ∧ messages = {}
  ∧ election_timer = [s ∈ Servers ↦ ElectionTimeout]
  ∧ heartbeat_timer = [s ∈ Servers ↦ HeartbeatInterval]
```

### The Leader-Election Process

Raft leader election can be written in stages.

**1. Election timeout**:

【Pseudo notation】
```tla
ElectionTimeout(s) ≜
  ∧ state[s] = Follower
  ∧ election_timer[s] = 0
  ∧ state' = [state EXCEPT ![s] = Candidate]
  ∧ currentTerm' = [currentTerm EXCEPT ![s] = @ + 1]
  ∧ votedFor' = [votedFor EXCEPT ![s] = s]
  ∧ SendRequestVoteRequests(s)
  ∧ election_timer' = [election_timer EXCEPT ![s] = ElectionTimeout]
  ∧ UNCHANGED ⟨log, commitIndex, nextIndex, matchIndex, heartbeat_timer⟩
```

**2. Sending vote requests**:

【Pseudo notation】
```tla
SendRequestVoteRequests(s) ≜
  messages' = messages ∪
    {[type ↦ "RequestVote",
      term ↦ currentTerm'[s],
      candidateId ↦ s,
      lastLogIndex ↦ Len(log[s]),
      lastLogTerm ↦ IF Len(log[s]) > 0 THEN log[s][Len(log[s])].term ELSE 0,
      dest ↦ t] : t ∈ Servers \ {s}}
```

**3. Processing vote responses**:

【Pseudo notation】
```tla
ReceiveRequestVoteResponse(s) ≜
  ∃ m ∈ messages :
    ∧ m.type = "RequestVoteResponse"
    ∧ m.dest = s
    ∧ m.term = currentTerm[s]
    ∧ m.voteGranted = TRUE
    ∧ state[s] = Candidate
    ∧ LET votes ≜ {t ∈ Servers : ∃ msg ∈ messages :
                     msg.type = "RequestVoteResponse" ∧
                     msg.dest = s ∧ msg.voteGranted = TRUE} ∪ {s}
       IN  ∧ Cardinality(votes) > Cardinality(Servers) ÷ 2
           ∧ state' = [state EXCEPT ![s] = Leader]
           ∧ SendHeartbeats(s)
           ∧ UNCHANGED ⟨currentTerm, votedFor, log, commitIndex⟩
```

### Log Replication

Once a leader exists, it accepts client requests and replicates them to the
followers as log entries.

**1. Appending an entry**:

【Pseudo notation】
```tla
AppendEntry(s, entry) ≜
  ∧ state[s] = Leader
  ∧ log' = [log EXCEPT ![s] = Append(@, entry)]
  ∧ SendAppendEntries(s)
  ∧ UNCHANGED ⟨currentTerm, votedFor, state, commitIndex⟩
```

**2. Sending `AppendEntries`**:

【Pseudo notation】
```tla
SendAppendEntries(s) ≜
  messages' = messages ∪
    {[type ↦ "AppendEntries",
      term ↦ currentTerm[s],
      leaderId ↦ s,
      prevLogIndex ↦ nextIndex[s][t] - 1,
      prevLogTerm ↦ IF nextIndex[s][t] > 1
                     THEN log[s][nextIndex[s][t] - 1].term
                     ELSE 0,
      entries ↦ SubSeq(log[s], nextIndex[s][t], Len(log[s])),
      leaderCommit ↦ commitIndex[s],
      dest ↦ t] : t ∈ Servers \ {s}}
```

**3. Processing responses and committing**:

【Pseudo notation】
```tla
ProcessAppendEntriesResponse(s) ≜
  ∃ m ∈ messages :
    ∧ m.type = "AppendEntriesResponse"
    ∧ m.dest = s
    ∧ state[s] = Leader
    ∧ m.term = currentTerm[s]
    ∧ IF m.success
       THEN ∧ nextIndex' = [nextIndex EXCEPT ![s][m.source] = m.matchIndex + 1]
            ∧ matchIndex' = [matchIndex EXCEPT ![s][m.source] = m.matchIndex]
            ∧ UpdateCommitIndex(s)
       ELSE ∧ nextIndex' = [nextIndex EXCEPT ![s][m.source] = Max(1, @ - 1)]
            ∧ UNCHANGED matchIndex
    ∧ UNCHANGED ⟨currentTerm, votedFor, log, state, commitIndex⟩
```

### Safety Guarantees

Raft should satisfy several important safety invariants.

【Pseudo notation】
```tla
LogMatching ≜
  ∀ s, t ∈ Servers, i ∈ DOMAIN log[s] ∩ DOMAIN log[t] :
    log[s][i].term = log[t][i].term ⟹
    ∀ j ∈ 1..i : log[s][j] = log[t][j]

LeaderUniqueness ≜
  ∀ s, t ∈ Servers :
    (state[s] = Leader ∧ state[t] = Leader) ⟹
    (s = t ∨ currentTerm[s] ≠ currentTerm[t])

CommittedEntriesNeverChange ≜
  ∀ s ∈ Servers, i ∈ 1..commitIndex[s] :
    □(log[s][i] = log'[s][i])
```

### Incorporating a Failure Model

A realistic distributed-system model must also include failures.

**Node failure**:

【Pseudo notation】
```tla
NodeFailure(s) ≜
  ∧ state[s] ≠ Failed
  ∧ state' = [state EXCEPT ![s] = Failed]
  ∧ UNCHANGED ⟨currentTerm, votedFor, log, commitIndex,
               nextIndex, matchIndex, messages⟩
```

**Network partition**:

【Pseudo notation】
```tla
NetworkPartition ≜
  ∃ partition ⊆ Servers :
    ∧ Cardinality(partition) > 0
    ∧ Cardinality(partition) < Cardinality(Servers)
    ∧ ∀ m ∈ messages :
        (m.source ∈ partition ∧ m.dest ∉ partition) ∨
        (m.source ∉ partition ∧ m.dest ∈ partition) ⟹
        m ∉ messages'
```

**Message loss**:

【Pseudo notation】
```tla
MessageLoss ≜
  ∃ m ∈ messages :
    ∧ messages' = messages \ {m}
    ∧ UNCHANGED ⟨currentTerm, votedFor, log, state, commitIndex,
                 nextIndex, matchIndex⟩
```

### Liveness Guarantees

Raft also aims to satisfy progress properties, subject to fairness and network
assumptions.

【Pseudo notation】
```tla
EventualLeaderElection ≜
  ◇(∃ s ∈ Servers : state[s] = Leader)

Progress ≜
  □(client_request ⟹ ◇committed)

Fairness ≜
  ∧ ∀ s ∈ Servers : WF_vars(ElectionTimeout(s))
  ∧ ∀ s ∈ Servers : WF_vars(ReceiveMessage(s))
  ∧ ∀ m ∈ MessageType : SF_vars(DeliverMessage(m))
```

### Verifying with TLC

A TLC configuration for a small Raft model might look as follows.

【Pseudo notation】
```text
\* Raft.cfg
CONSTANTS
  Servers = {"s1", "s2", "s3"}
  ElectionTimeout = 3
  HeartbeatInterval = 1
  MaxLogLength = 5

SPECIFICATION
  Init ∧ □[Next]_vars ∧ Fairness

INVARIANTS
  TypeInvariant
  LogMatching
  LeaderUniqueness
  CommittedEntriesNeverChange

PROPERTIES
  EventualLeaderElection
  Progress
```

This kind of model lets us check the essential correctness of the algorithm on a
small cluster, including various fault scenarios.

The broader lesson is that even a complicated protocol such as distributed
consensus can be written precisely in TLA+ and then checked automatically. That
combination of mathematical clarity and practical verification is one of the
main reasons TLA+ is valuable for real systems.

---

## End-of-Chapter Exercises

**Submission rules when using AI**

- Treat AI output as a proposal; the final judgment must come from a verifier.
- Submit the prompt used, the generated specification and invariants, the
  verification commands and logs (including seed, depth, and scope), and the
  repair history if a counterexample was found.
- For detailed templates, see Appendix D and Appendix F.

### Basic Exercise 1: Understanding Temporal-Logic Notation

Explain the following temporal formulas in plain language and give a concrete
example of each in a real system.

1. `□(resource_requested ⟹ ◇resource_granted)`
2. `◇□(system_stable)`
3. `□◇(garbage_collection)`
4. `(critical_section_entered) ~> (critical_section_exited)`

For each formula, provide:

- an explanation of its meaning;
- a concrete real-system example; and
- an example of a situation in which the property is violated.

### Basic Exercise 2: Describing State and Action

Describe the following system in terms of TLA+ state and actions.

**Simple inventory-management system**:

- a variable `stock` stores the current quantity;
- a restock operation increases the quantity;
- a shipment operation decreases the quantity but cannot execute when stock is
  insufficient; and
- a stocktaking operation corrects the quantity to the accurate value.

Describe:

1. the variable declarations and type invariant;
2. the initial state;
3. the action definition for each operation;
4. the `Next` predicate; and
5. a basic safety invariant.

### Practical Exercise 1: Designing a Mutual-Exclusion Protocol

Write Peterson's algorithm in TLA+ and verify it with TLC.

**Requirements**:

- two processes use mutual exclusion;
- each process has the states "noncritical," "trying," and "critical"; and
- the protocol is controlled by a flag array and a turn variable.

**Properties to verify**:

1. mutual exclusion: the two processes are never in the critical section at the
   same time;
2. progress: if there is a pending request, eventually some process enters the
   critical section; and
3. fairness: both processes can enter the critical section repeatedly rather
   than one starving forever.

### Practical Exercise 2: The Producer-Consumer Problem

Design a producer-consumer system with a finite buffer in TLA+.

**System structure**:

- multiple producer processes;
- multiple consumer processes; and
- a shared fixed-size buffer.

**Constraints**:

- producers must wait when the buffer is full;
- consumers must wait when the buffer is empty; and
- FIFO order must be preserved.

**Verification targets**:

1. absence of deadlock;
2. no data loss;
3. fairness between producers and consumers; and
4. avoidance of buffer overflow and underflow.

### Advanced Exercise: Designing a Distributed System

Design a simplified distributed file system in TLA+.

**System requirements**:

- multiple storage nodes;
- replication for redundancy;
- client read and write requests; and
- tolerance to node failure.

**Main operations**:

1. file creation and deletion;
2. file reading and writing;
3. replication management; and
4. failure detection and recovery.

**Properties to verify**:

1. **Consistency**: all replicas eventually hold the same contents.
2. **Availability**: service continues despite some node failures.
3. **Durability**: data remains persistently stored.
4. **Partition tolerance**: the system behaves appropriately under network
   partition.

**Design questions**:

- How is the failure model defined?
- Which consistency model is chosen: strong consistency or eventual
  consistency?
- Is distributed consensus required, and if so, which algorithm should be
  chosen?
- How are performance trade-offs handled?

Through these exercises, you should gain practical skill in formal distributed
system design with TLA+. In the advanced exercise in particular, it is
important to reason explicitly about the implications of CAP-style constraints
and the trade-offs between theory and practice.
