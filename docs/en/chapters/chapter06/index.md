---
layout: book
title: "Chapter 6: Process-Centric Description: Concurrent Systems with CSP"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter06.md"
---
# Chapter 6: Process-Centric Description: Concurrent Systems with CSP

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter06.md`

This chapter uses two kinds of code examples.

- **Tool-compliant blocks**: examples intended to be syntactically valid
  CSPM for FDR, using ASCII notation such as `->`, `[]`, `|||`, `[| X |]`, and
  `P[[a <- b]]`
- **Pseudo-notation blocks**: simplified explanatory notation. Unicode symbols such as
  `→`, `□`, and `⊓`, along with some guards, `where` clauses, and event
  parameter conventions, do not necessarily match CSPM exactly and should not be
  pasted into a tool unchanged

## 6.1 The Essence of Concurrency: Why It Is Hard

### The Limits of Sequential Thinking

The human brain is basically adapted to sequential reasoning. We are good at
thinking about one thing after another and advancing a line of logic step by
step. That pattern works very well for single-process programs. A flow such as
"do A, then B, and based on the result do C or D" is easy to understand.

Concurrent systems are different. Multiple events progress at the same time. In
a restaurant, several chefs may be cooking different dishes in parallel while
several waiters are serving different tables. Understanding that web of
interaction through purely sequential reasoning is difficult.

The core difficulty of concurrency is combinatorial explosion in the possible
execution patterns. If two processes each perform three operations, there may
already be twenty possible interleavings. As the number of processes and the
number of operations per process grow, that number increases rapidly.

### Emergent Complexity Caused by Interaction

One of the most interesting and difficult features of concurrent systems is
that each individual process may be simple while the interaction among them
creates unexpected complexity. This is similar to many-body problems in physics
or collective behavior in biology.

Consider two processes trying to access the same resource. Each process may be
perfectly correct in isolation, yet simultaneous execution can lead to a race
condition and produce an unexpected result.

【擬似記法】
```text
Process A: read the resource → update the value → write the resource
Process B: read the resource → update the value → write the resource
```

If these actions interleave in the wrong way, one update may overwrite the
other, causing inconsistent data.

### Nondeterminism as Reality

In concurrent systems, nondeterminism is unavoidable. The same initial state
may lead to different results depending on scheduling and timing. This makes
behavior harder to predict and debugging harder to perform.

Nondeterminism is not purely negative. It can also support flexibility and
performance. The real design challenge is to control it while still ensuring
safety and liveness.

![Figure 6-1: Basic concepts of concurrent systems and communication models in CSP]({{ '/assets/images/diagrams/csp-concurrency-concepts-en.svg' | relative_url }})

### The Growing Complexity of Time and Causality

In a sequential system, temporal order and causality are relatively clear. If A
happens before B, then A can be a cause of B. In a concurrent system, physical
time and logical time become less aligned, and causal relations become harder
to reason about.

The problem becomes even more serious in distributed systems. Clock
synchronization across nodes is difficult, and even the notion of "simultaneous"
becomes slippery. In much the same way that relativity complicated the notion
of absolute time in physics, distributed systems force us to reason without a
single universal clock.

### Partial Failure

In concurrent and distributed systems, one part of the system may fail while the
rest continues to operate. This is called *partial failure*, and it introduces
another layer of design complexity.

In a conventional sequential system, failure is often global: the whole program
crashes. In a distributed system, by contrast, part of the network may be cut
off while the remaining nodes continue to run. Maintaining consistency in such
a situation is a major design challenge.

### The Benefits of Concurrency

Despite these difficulties, concurrency is indispensable in modern systems.
There are clear reasons for that.

- **Higher performance**: multiple CPU cores can be used effectively.
- **Better responsiveness**: background work can proceed without blocking the
  user interface.
- **Scalability**: capacity can be expanded horizontally.
- **Availability**: the system can tolerate some local failures.
- **Natural modeling**: many real-world activities are inherently concurrent.

Designing concurrent systems is difficult, but with the right abstraction and
formal methods, their complexity can be managed. CSP is one of the strongest
tools for doing so.

## 6.2 The CSP Worldview: Processes and Communication

### Tony Hoare's Insight

CSP, or *Communicating Sequential Processes*, was introduced by Tony Hoare in
1978. Hoare's central insight was that the essence of concurrency lies in
communication. The overall behavior of the system depends on how processes
exchange messages and synchronize.

This was a major shift in perspective. Earlier approaches to concurrency often
focused on shared memory and shared variables. Hoare argued that explicit
message passing provides a better abstraction for understanding and designing
concurrent systems.

### The Abstraction of a Process

In CSP, a process is a sequentially executed pattern of behavior. The important
point is that the inside of a process can still be understood in the familiar
way: step by step. The complexity is concentrated in the interactions among
processes.

That separation allows us to reason independently about the correctness of a
single process and the correctness of process interaction. This is a crucial
principle for managing complexity.

【擬似記法】
```csp
VENDING_MACHINE = coin → (tea → VENDING_MACHINE | coffee → VENDING_MACHINE)
```

This expression says that a vending-machine process accepts a coin, then allows
the choice of tea or coffee, and finally returns to its original state.

### Interaction Through Events

In CSP, interaction among processes is abstracted as *events*. An event may
represent message exchange, synchronization, access to a resource, or some
other interaction. CSP treats them in one uniform way.

The crucial property of an event is synchrony. An event occurs only when all
processes involved in that event are ready. That makes coordination explicit.

【擬似記法】
```csp
CUSTOMER = arrive → order → pay → leave → CUSTOMER
CASHIER = greet → order → pay → CASHIER

SYSTEM = CUSTOMER [| {order, pay} |] CASHIER
```

Because `order` and `pay` appear in both processes and are included in the
synchronization set, they occur as rendezvous events. Events with different
names do not synchronize automatically. If synchronization is required, names
must be aligned explicitly or adjusted through renaming.

### Structuring Communication with Channels

Real systems often contain many interacting processes. CSP uses *channels* to
structure that interaction. A channel is an abstract route over which messages
move between processes.

【ツール準拠（そのまま動く）】
```csp
channel in, out : {0..1}

PRODUCER = in!0 -> PRODUCER
BUFFER = in?x -> out!x -> BUFFER
CONSUMER = out?x -> CONSUMER

SYSTEM = (PRODUCER [| {|in|} |] BUFFER) [| {|out|} |] CONSUMER
```

In this example, `PRODUCER` synchronizes with `BUFFER` on `in`, and `BUFFER`
synchronizes with `CONSUMER` on `out`. The communication structure is visible
in the process composition itself.

### Building Systems Hierarchically

One of the strengths of CSP is compositionality. Small processes can be
combined to form larger systems. This hierarchical construction allows large
systems to be decomposed into understandable pieces.

【擬似記法】
```csp
CELL = left?x → right!x → CELL
PIPE(n) = if n = 0 then CELL
          else CELL [| {right, left} |] PIPE(n-1)
```

This recursive definition constructs a pipeline of arbitrary length.

### Integrating Choice and Concurrency

CSP treats choice and concurrency within one unified framework.

**External choice (`□`)**: the environment determines which branch is taken.

【擬似記法】
```csp
ATM = card_insert → (pin_correct → transaction □ pin_incorrect → reject)
```

**Internal choice (`⊓`)**: the process chooses nondeterministically.

【擬似記法】
```csp
RANDOM = heads → SUCCESS ⊓ tails → FAILURE
```

**Parallel composition**: multiple processes run concurrently.

【ツール準拠（そのまま動く）】
```csp
PROCESS1 = a -> PROCESS1
PROCESS2 = b -> PROCESS2
PROCESS3 = c -> PROCESS3

SYSTEM = PROCESS1 || PROCESS2 || PROCESS3
```

### The Benefit of Time Abstraction

CSP abstracts away from concrete execution time and focuses on the ordering of
events. This abstraction makes it possible to analyze essential system behavior
without being distracted by low-level timing details.

When necessary, timing constraints can still be introduced. Timed variants of
CSP make durations and deadlines explicit. But the untimed form is valuable
precisely because it isolates the logical structure of concurrency first.

### Handling Failure and Exceptions

CSP can express not only normal behavior but also faults and exceptional cases.
A fault can be treated as just another kind of event, which means failure
handling can be integrated into the same control structure as normal behavior.

【擬似記法】
```csp
RELIABLE_SERVICE =
  request → (
    success → response → RELIABLE_SERVICE
    □
    failure → retry → RELIABLE_SERVICE
    □
    timeout → abort → RELIABLE_SERVICE
  )
```

This unified treatment makes it easier to reason about robustness at the design
stage.

## 6.3 Basic Processes and Their Composition

### Primitive Processes

All the richer systems described in CSP are built from a small number of basic
processes. Understanding these primitives is the foundation of the notation.

**`STOP`**: a process that does nothing and cannot proceed, representing a
deadlock state.

【ツール準拠（そのまま動く）】
```csp
STOP
```

**`SKIP`**: a process that terminates successfully.

【ツール準拠（そのまま動く）】
```csp
SKIP
```

**Simple event processes**:

【擬似記法】
```csp
a → STOP

a → b → STOP
```

These primitives are like notes in music: by combining a small vocabulary, we
obtain rich behavior.

### The Prefix Operator (`→`)

The prefix operator is the most basic constructor in CSP. It means that after a
certain event occurs, the process behaves in a specified way.

【擬似記法】
```csp
coin → (tea → STOP | coffee → STOP)
```

This means that after a coin is inserted, tea or coffee can be selected.

A crucial feature of prefix is that the process waits until the specified event
can occur. That waiting behavior is where synchronization becomes visible.

### Choice Operators

CSP has several forms of choice, and it is important to understand their
semantics.

**External choice (`□`)**: the environment chooses.

【擬似記法】
```csp
ATM = card_insert → pin_entry □ admin_key → maintenance_mode
```

Here, the environment determines whether a customer inserts a card or an
administrator enters maintenance mode.

**Internal choice (`⊓`)**: the process chooses nondeterministically.

【擬似記法】
```csp
COIN_FLIP = heads → WIN ⊓ tails → LOSE
```

**Guarded choice**:

【擬似記法】
```csp
BUFFER = size < MAX & input?x → add.x → BUFFER
        □ size > 0 & output!first → remove → BUFFER
```

A guarded branch is available only when its condition holds.

### Parallel Composition Operators

The family of operators for parallel composition is central to CSP.

**Independent parallel (`|||`)**: processes run independently.

【ツール準拠（そのまま動く）】
```csp
PRINTER = print_job -> PRINTER
SCANNER = scan_doc -> SCANNER
KEYBOARD = key_press -> KEYBOARD

SYSTEM = PRINTER ||| SCANNER ||| KEYBOARD
```

These processes do not interact and may proceed independently.

**Synchronized parallel (`[| X |]`)**: processes synchronize on a chosen set of
events.

【ツール準拠（そのまま動く）】
```csp
CUSTOMER = arrive -> order -> pay -> leave -> CUSTOMER
CASHIER = greet -> order -> pay -> CASHIER

SYSTEM = CUSTOMER [| {order, pay} |] CASHIER
```

The events `order` and `pay` must occur jointly, while the others proceed
independently.

**Interleaving**: the events of processes may be interwoven in any order.

【擬似記法】
```csp
AB_SEQUENCE = A ||| B
where A = a → b → A
      B = c → d → B
```

### Pipeline Composition

Pipelines are a standard way to describe staged data flow among processes.

【擬似記法】
```csp
PRODUCER = produce.data → c12!data → PRODUCER
PROCESSOR = c12?x → process.x → c23!process(x) → PROCESSOR
CONSUMER = c23?x → consume.x → CONSUMER

PIPELINE = (PRODUCER [| {c12} |] PROCESSOR)
           [| {c23} |] CONSUMER
```

The producer, processor, and consumer are connected through intermediate
channels.

### Infinite Processes Through Recursion

Many practical systems must run indefinitely. CSP expresses such behavior
naturally through recursion.

**Simple recursion**:

【擬似記法】
```csp
CLOCK = tick → CLOCK
```

**Recursion with state**:

【擬似記法】
```csp
COUNTER(n) = up → COUNTER(n+1)
           □ down → COUNTER(n-1)
           □ reset → COUNTER(0)
```

**Mutual recursion**:

【擬似記法】
```csp
PING = ping → PONG
PONG = pong → PING
```

### Process Families

When many similar processes are needed, process families offer a compact way to
define them.

【擬似記法】
```csp
WORKER(id) = task?t → process.id.t → result!process(t) → WORKER(id)
WORKERS = ||| i:{1..N} @ WORKER(i)
```

This defines `N` worker processes running concurrently.

### Hiding and Abstraction

To conceal internal events from the external interface, CSP provides the hiding
operator (`\`).

【ツール準拠（そのまま動く）】
```csp
INTERNAL_PROCESS = internal_event1 -> internal_event2 -> external_event -> INTERNAL_PROCESS
PUBLIC_INTERFACE = INTERNAL_PROCESS \ {internal_event1, internal_event2}
```

This exposes only the public behavior while suppressing internal details.

### Renaming

CSP also supports renaming, which is useful for reusing generic processes in a
more specific setting.

【ツール準拠（そのまま動く）】
```csp
channel in, out : {0..1}
channel input, output : {0..1}

GENERIC_BUFFER = in?x -> out!x -> GENERIC_BUFFER
SPECIFIC_BUFFER = GENERIC_BUFFER[[in <- input, out <- output]]
```

### Design Principles for Process Composition

Useful principles for composing CSP processes include the following.

1. **Minimal interfaces**: synchronize only where necessary.
2. **Symmetry**: use symmetric designs where possible.
3. **Reuse**: write generic process definitions.
4. **Stepwise refinement**: move gradually from abstraction to detail.

These principles help produce concurrent designs that remain understandable and
maintainable.

## 6.4 Synchronization and Communication

### The Essential Meaning of Synchronization

Synchronization is one of the core concepts in concurrent systems. In CSP, it
means that multiple processes coordinate at a particular event. The analogy is
an orchestra following a conductor or dancers moving together to the same beat.

CSP uses a rendezvous-style notion of synchronization. An event can occur only
when all processes involved in that event are ready. That requirement expresses
coordination directly.

### How Channel Communication Works

CSP models communication through channels.

**Output (`!`)**: send a message.

【擬似記法】
```csp
SENDER = ch!message → SENDER
```

**Input (`?`)**: receive a message.

【擬似記法】
```csp
RECEIVER = ch?x → process.x → RECEIVER
```

**Synchronous communication**: send and receive occur together.

【ツール準拠（そのまま動く）】
```csp
channel ch : {0..1}

SENDER = ch!0 -> SENDER
RECEIVER = ch?x -> RECEIVER

COMMUNICATION = SENDER [| {|ch|} |] RECEIVER
```

In this abstraction, send and receive are one synchronized event. If real
systems must model loss, delay, retransmission, or buffering, those phenomena
need to be represented explicitly.

### The Idea of Buffering

Real communication often requires buffering. In CSP, a buffer can itself be
modeled as a process.

**Single-element buffer**:

【擬似記法】
```csp
BUFFER1 = in?x → out!x → BUFFER1
```

**Buffer of capacity `N`**:

【擬似記法】
```csp
BUFFER(n) = (n > 0) & out!front → BUFFER(n-1)
          □ (n < MAX) & in?x → BUFFER(n+1)
```

**FIFO buffer**:

【擬似記法】
```csp
FIFO_BUFFER(queue) =
  (queue ≠ ⟨⟩) & out!head(queue) → FIFO_BUFFER(tail(queue))
  □ (len(queue) < MAX) & in?x → FIFO_BUFFER(queue ⌢ ⟨x⟩)
```

### Priority-Based Communication

Some systems need message priorities.

【擬似記法】
```csp
PRIORITY_HANDLER =
  urgent?x → handle_urgent.x → PRIORITY_HANDLER
  □ normal?y → handle_normal.y → PRIORITY_HANDLER
  where urgent has priority over normal
```

### Broadcast Communication

Sometimes a single message must be delivered to multiple receivers.

【擬似記法】
```csp
BROADCASTER = message?x → (out1!x || out2!x || out3!x) → BROADCASTER

MULTICAST_SYSTEM = BROADCASTER
                 [| {out1} |] RECEIVER1
                 [| {out2} |] RECEIVER2
                 [| {out3} |] RECEIVER3
```

### Selective Communication

A router-like process may choose the communication partner based on the
message's destination.

【擬似記法】
```csp
ROUTER =
  input?msg → (
    (destination(msg) = A) & to_A!msg → ROUTER
    □ (destination(msg) = B) & to_B!msg → ROUTER
    □ (destination(msg) = C) & to_C!msg → ROUTER
  )
```

### Communication with Timeouts

Real systems also need to cope with delay and failure.

【擬似記法】
```csp
RELIABLE_SENDER =
  send!message → (
    ack → SUCCESS
    □ timeout → retry → RELIABLE_SENDER
  )
```

### Handshake Protocols

More elaborate communication often requires multi-stage handshakes.

【擬似記法】
```csp
CLIENT = request!req → response?res → CLIENT
SERVER = request?req → process.req → response!result → SERVER

THREE_WAY_HANDSHAKE =
  syn → syn_ack → ack → ESTABLISHED
```

### Classes of Synchronization Patterns

Synchronization patterns in CSP include the following.

- **One-to-one communication**: simple point-to-point messaging
- **One-to-many communication**: broadcast or multicast
- **Many-to-one communication**: multiple senders to one receiver
- **Many-to-many communication**: richer network-style interaction

**Barrier synchronization**:

【擬似記法】
```csp
BARRIER(n) =
  (n > 1) & arrive → BARRIER(n-1)
  □ (n = 1) & arrive → release → BARRIER(N)
```

### The Leader-Follower Pattern

Hierarchical control structures can also be modeled directly.

【擬似記法】
```csp
LEADER =
  decision!cmd → (
    follower1.ack → follower2.ack → follower3.ack → commit
  ) → LEADER

FOLLOWER(id) =
  decision?cmd → execute.cmd → ack → FOLLOWER(id)
```

### Voting Protocols

Agreement protocols in distributed systems can be captured as CSP processes.

【擬似記法】
```csp
VOTER(id) = vote_request?proposal →
           (approve!id → VOTER(id) □ reject!id → VOTER(id))

COORDINATOR =
  broadcast_proposal →
  collect_votes →
  (majority_approve & commit □ majority_reject & abort) →
  COORDINATOR
```

### Communication Reliability

Practical systems often require explicit handling of communication failures.

**Message loss**:

【擬似記法】
```csp
LOSSY_CHANNEL = msg?x → (deliver!x □ lose → SKIP) → LOSSY_CHANNEL
```

**Duplicate elimination**:

【擬似記法】
```csp
DEDUP_RECEIVER =
  msg?x → (
    (x ∉ received) & process.x → DEDUP_RECEIVER[received ∪ {x}]
    □ (x ∈ received) & duplicate → DEDUP_RECEIVER
  )
```

**Ordering guarantee**:

【擬似記法】
```csp
ORDERED_DELIVERY =
  in?⟨seq, msg⟩ → (
    (seq = expected) & out!msg → ORDERED_DELIVERY[expected+1]
    □ (seq ≠ expected) & buffer.⟨seq,msg⟩ → ORDERED_DELIVERY
  )
```

By combining such communication patterns, CSP can describe the behavior of
realistic distributed systems in a disciplined way.

## 6.5 Deadlock and Liveness: The Pathology of Systems

### Deadlock as a Pathological Phenomenon

Deadlock is one of the most serious problems in a concurrent system. Multiple
processes wait for one another, and the entire system reaches a state in which
no useful progress is possible. A familiar analogy is four cars stuck at an
intersection, each waiting for another to move first.

In CSP, deadlock can be defined formally. The system is deadlocked when every
participating process is waiting for an event that another waiting process would
have to initiate.

【擬似記法】
```csp
DEADLOCK_EXAMPLE =
  (a → b → STOP) [| {a, b} |] (b → a → STOP)
```

Here, the left process waits for `a` while the right process waits for `b`, so
neither can move.

### The Four Conditions for Deadlock

Classical results say that four conditions are jointly necessary for deadlock.

1. **Mutual exclusion**: a resource cannot be used simultaneously by multiple
   processes.
2. **Hold and wait**: a process holds one resource while waiting for another.
3. **No preemption**: resources cannot be forcibly taken away.
4. **Circular wait**: there is a cycle in the wait-for relation.

CSP can describe these conditions explicitly.

【擬似記法】
```csp
RESOURCE = acquire → use → release → RESOURCE

PROCESS = resource1.acquire → resource2.acquire →
          work → resource2.release → resource1.release → PROCESS

SYSTEM = (P1 [| {r1,r2} |] P2) \ {r1,r2}
where P1 = r1.acquire → r2.acquire → work → r2.release → r1.release → P1
      P2 = r2.acquire → r1.acquire → work → r1.release → r2.release → P2
```

### Deadlock Avoidance Strategies

To avoid deadlock, at least one of the four conditions must be broken.

**Resource ordering**:

【擬似記法】
```csp
ORDERED_PROCESS =
  (id(r1) < id(r2)) & r1.acquire → r2.acquire → work →
  r2.release → r1.release → ORDERED_PROCESS
```

If all processes acquire resources in the same global order, circular wait can
be prevented.

**Timeout mechanism**:

【擬似記法】
```csp
TIMEOUT_PROCESS =
  r1.acquire → (
    r2.acquire → work → r2.release → r1.release → TIMEOUT_PROCESS
    □ timeout → r1.release → retry → TIMEOUT_PROCESS
  )
```

**Banker's algorithm**:

【擬似記法】
```csp
BANKER =
  request?⟨pid, resource⟩ → (
    safe_state(allocate(pid, resource)) & grant!pid → BANKER
    □ ¬safe_state(allocate(pid, resource)) & deny!pid → BANKER
  )
```

### Livelock as a More Subtle Problem

Livelock is different from deadlock. The system is active, but not making real
progress. A common analogy is two people in a narrow corridor repeatedly trying
to step aside in the same direction.

【擬似記法】
```csp
LIVELOCK_EXAMPLE =
  P1 [| {move} |] P2
where P1 = move.left → detect_collision → move.right → P1
      P2 = move.right → detect_collision → move.left → P2
```

### Guaranteeing Liveness

Liveness means that "something good eventually happens." In CSP, liveness can
be analyzed from several perspectives.

**Starvation freedom**: every process eventually makes progress.

【擬似記法】
```csp
FAIR_SCHEDULER =
  schedule!p1 → schedule!p2 → schedule!p3 → FAIR_SCHEDULER
```

**Fairness**: a process that continually has the opportunity to proceed is
ultimately allowed to do so.

【擬似記法】
```csp
FAIR_ACCESS =
  (request.p1 → grant.p1 → FAIR_ACCESS) |||
  (request.p2 → grant.p2 → FAIR_ACCESS) |||
  FAIRNESS_CONSTRAINT
```

### Formalizing Progress Conditions

Progress guarantees can also be written abstractly.

**Minimal progress guarantee**:

【擬似記法】
```text
PROGRESS = □◊(progress_event)
```

This reads as: always, eventually, a progress event occurs.

**Bounded waiting**:

【擬似記法】
```text
BOUNDED_WAIT = request → ◊≤n(grant)
```

This expresses that after a request, permission is granted within at most `n`
time units.

### Detection and Recovery

Detection and recovery mechanisms are also important parts of a practical
system.

**Deadlock detector**:

【擬似記法】
```csp
DETECTOR =
  monitor_state → (
    deadlock_detected & recovery_action → DETECTOR
    □ normal_state & continue → DETECTOR
  )
```

**Recovery strategies**:

【擬似記法】
```csp
RECOVERY =
  abort_victim → rollback → restart → RECOVERY
  □ preempt_resource → reassign → RECOVERY
```

### The Dining Philosophers Problem

A classic illustration of deadlock is the dining philosophers problem.

【擬似記法】
```csp
PHILOSOPHER(i) =
  pickup.left(i) → pickup.right(i) → eat →
  putdown.right(i) → putdown.left(i) → think → PHILOSOPHER(i)

DINING_PHILOSOPHERS =
  ||| i:{1..5} @ PHILOSOPHER(i)

PHILOSOPHER_FIXED(i) =
  (i < 5) & pickup.left(i) → pickup.right(i) → eat →
           putdown.right(i) → putdown.left(i) → think → PHILOSOPHER_FIXED(i)
  □ (i = 5) & pickup.right(i) → pickup.left(i) → eat →
              putdown.left(i) → putdown.right(i) → think → PHILOSOPHER_FIXED(i)

WAITER =
  request.i → (
    available_forks(i) & grant.i → WAITER
    □ ¬available_forks(i) & wait.i → WAITER
  )
```

The example illustrates both a problematic design and two standard remedies:
asymmetric acquisition order and waiter-based control.

### Impact on Performance

Deadlock-avoidance measures often have performance costs.

- **Conservative strategies** are safe but may reduce efficiency.
- **Optimistic strategies** are efficient but may incur higher recovery cost.
- **Adaptive strategies** switch behavior depending on load or contention.

【擬似記法】
```csp
ADAPTIVE_SYSTEM =
  low_contention & OPTIMISTIC_PROTOCOL
  □ high_contention & CONSERVATIVE_PROTOCOL
```

### Tool-Based Verification

Dedicated tools can analyze CSP models for deadlock and related properties.

- **FDR (Failures-Divergences Refinement)**: rigorous model checking and
  refinement analysis
- **ProB**: model checking and animation support
- **PAT**: support for richer verification scenarios, including probabilistic
  reasoning

These tools allow deadlock risks to be discovered and corrected while the
system is still at the design stage.

## 6.6 Learning Through an Example: Designing a Restaurant System

### Organizing the System Requirements

A restaurant system is a strong example for concurrent design. Multiple roles —
customers, waiters, chefs, and cashiers — must coordinate while sharing limited
resources such as tables, kitchen equipment, and ingredients.

**Main actors**:

- customers;
- waiters;
- chefs;
- cashier; and
- manager.

**Shared resources**:

- tables;
- kitchen equipment;
- ingredient inventory; and
- menu information.

**Main processes**:

1. customer arrival and seating;
2. order intake and transmission to the kitchen;
3. cooking and serving; and
4. billing and departure.

### Defining Basic Processes

We can begin by describing the basic behavior of each role.

【擬似記法】
```csp
CUSTOMER(id) =
  arrive → wait_for_table →
  seat.id → browse_menu → order.id →
  wait_for_food → eat → request_bill →
  pay → leave → CUSTOMER(id)

WAITER(id) =
  greet_customer → take_order →
  transmit_to_kitchen → serve_food →
  present_bill → process_payment →
  clean_table → WAITER(id)

CHEF(id) =
  receive_order → check_ingredients →
  cook → plate_food → ready_for_service →
  CHEF(id)

CASHIER =
  receive_payment_request → calculate_total →
  process_payment → issue_receipt → CASHIER
```

### The Table-Management Subsystem

Table assignment is a core subsystem. A limited number of seats must be managed
efficiently while avoiding coordination problems.

【擬似記法】
```csp
TABLE_MANAGER =
  customer_arrives → (
    available_table & assign_table → TABLE_MANAGER
    □ no_available_table & add_to_waitlist → TABLE_MANAGER
  )
  □ table_freed → update_availability →
    (waitlist_empty & TABLE_MANAGER
     □ waitlist_not_empty & serve_next_customer → TABLE_MANAGER)

TABLE(id) =
  reserve.id → occupied.id →
  serve.id → eating.id →
  clear.id → clean.id → TABLE(id)

RESTAURANT_TABLES =
  ||| table_id:{1..N} @ TABLE(table_id)
```

### The Order-Processing Workflow

Order processing from intake through serving can be described as a set of
cooperating concurrent processes.

【擬似記法】
```csp
ORDER_TAKING =
  customer_ready → approach_table →
  present_menu → answer_questions →
  take_order → confirm_order →
  transmit_to_kitchen → ORDER_TAKING

KITCHEN_ORDER_MANAGER =
  new_order?order → (
    ingredients_available(order) &
    assign_to_chef!order → KITCHEN_ORDER_MANAGER
    □ ingredients_unavailable(order) &
    inform_shortage → KITCHEN_ORDER_MANAGER
  )

COOKING_PROCESS(chef_id) =
  assigned_order?order →
  gather_ingredients.order →
  cook.order →
  quality_check.order →
  ready_for_pickup!order →
  COOKING_PROCESS(chef_id)

FOOD_SERVICE =
  food_ready?order →
  locate_customer.order →
  deliver_food.order →
  check_satisfaction →
  FOOD_SERVICE
```

### Resource Management for Kitchen Equipment

Kitchen equipment such as stoves and ovens must be managed with mutual
exclusion.

【擬似記法】
```csp
EQUIPMENT_MANAGER =
  request_equipment?⟨chef, equipment⟩ → (
    equipment_available(equipment) &
    grant_access!⟨chef, equipment⟩ → EQUIPMENT_MANAGER
    □ equipment_busy(equipment) &
    queue_request!⟨chef, equipment⟩ → EQUIPMENT_MANAGER
  )
  □ release_equipment?⟨chef, equipment⟩ →
    update_availability →
    serve_next_request → EQUIPMENT_MANAGER

STOVE(id) =
  reserve.id → cooking.id → release.id → STOVE(id)

OVEN(id) =
  preheat.id → reserve.id → baking.id → release.id → OVEN(id)

KITCHEN_EQUIPMENT =
  (||| stove_id:{1..4} @ STOVE(stove_id))
  |||
  (||| oven_id:{1..2} @ OVEN(oven_id))
```

### The Inventory-Management System

Ingredient inventory and replenishment also form an important concurrent
subsystem.

【擬似記法】
```csp
INVENTORY_MANAGER =
  use_ingredient?⟨ingredient, quantity⟩ → (
    sufficient_stock(ingredient, quantity) &
    update_stock → check_reorder_level →
    (below_threshold & trigger_reorder □ adequate_stock & SKIP) →
    INVENTORY_MANAGER
    □ insufficient_stock(ingredient, quantity) &
    report_shortage → INVENTORY_MANAGER
  )
  □ receive_delivery?⟨ingredient, quantity⟩ →
    update_stock → INVENTORY_MANAGER

AUTO_ORDERING =
  check_inventory → (
    reorder_needed & place_order → wait_for_delivery → AUTO_ORDERING
    □ stock_adequate & schedule_next_check → AUTO_ORDERING
  )
```

### The Payment-Processing System

A practical restaurant must also support several payment methods.

【擬似記法】
```csp
PAYMENT_PROCESSING =
  payment_request?⟨table, amount⟩ →
  calculate_total.amount →
  present_payment_options →
  (cash_payment → process_cash → issue_receipt → PAYMENT_PROCESSING
   □ card_payment → process_card →
     (transaction_approved & issue_receipt → PAYMENT_PROCESSING
      □ transaction_declined & request_alternative → PAYMENT_PROCESSING)
   □ digital_payment → process_digital →
     verify_payment → issue_receipt → PAYMENT_PROCESSING)

ACCOUNTING_SYSTEM =
  transaction_completed?details →
  record_sale → update_daily_total →
  (end_of_day & generate_report □ continue_operation) →
  ACCOUNTING_SYSTEM
```

### Emergency Handling

Emergency cases such as food-safety incidents or fire must also be represented.

【擬似記法】
```csp
EMERGENCY_SYSTEM =
  (fire_alarm → evacuate_all → shutdown_equipment → EMERGENCY_SYSTEM
   □ food_safety_issue → stop_affected_orders → investigate → EMERGENCY_SYSTEM
   □ power_outage → emergency_lighting → preserve_cold_storage → EMERGENCY_SYSTEM
   □ normal_operation → monitor → EMERGENCY_SYSTEM)

EVACUATION_PROTOCOL =
  emergency_detected →
  sound_alarm →
  (guide_customers_out ||| secure_premises ||| contact_authorities) →
  all_clear → resume_operations → EVACUATION_PROTOCOL
```

### Integrating the Whole System

Once the subsystems are defined, they can be composed into one whole system.

【擬似記法】
The following is a conceptual composition example. Because several process
definitions are omitted, it should not be treated as executable CSPM as-is.

```csp
RESTAURANT_SYSTEM =
  (CUSTOMER_MANAGEMENT
   [| {arrive, seat, order, pay, leave} |]
   STAFF_COORDINATION)
  [| {order, food_ready, payment} |]
  (KITCHEN_OPERATIONS
   [| {ingredients, equipment} |]
   RESOURCE_MANAGEMENT)
  \ {internal_communications}

where
  CUSTOMER_MANAGEMENT = ||| id:{1..MAX_CUSTOMERS} @ CUSTOMER(id)
  STAFF_COORDINATION =
    (||| id:{1..N_WAITERS} @ WAITER(id)) |||
    (||| id:{1..N_CHEFS} @ CHEF(id)) |||
    CASHIER
  KITCHEN_OPERATIONS =
    KITCHEN_ORDER_MANAGER |||
    (||| id:{1..N_CHEFS} @ COOKING_PROCESS(id))
  RESOURCE_MANAGEMENT =
    INVENTORY_MANAGER |||
    EQUIPMENT_MANAGER |||
    TABLE_MANAGER
```

### Considering Performance Optimization

A practical system must also address performance.

【擬似記法】
```csp
LOAD_BALANCER =
  new_order?order → (
    find_least_busy_chef →
    assign_order!⟨chef, order⟩ → LOAD_BALANCER
  )

PEAK_TIME_MANAGEMENT =
  detect_rush_hour →
  (increase_staff ||| prioritize_fast_orders ||| optimize_seating) →
  monitor_queue_length →
  (acceptable_wait_time & continue □ excessive_wait & escalate) →
  PEAK_TIME_MANAGEMENT
```

### Properties That Should Be Verified

Important verification targets for the restaurant system include the following.

**Safety**:

- absence of deadlock;
- correct mutual exclusion on shared resources; and
- adherence to food-safety rules.

**Liveness**:

- every customer is eventually served;
- orders do not remain delayed forever; and
- equipment is not occupied forever without progress.

**Fairness**:

- service follows a fair queueing policy;
- staff workload is balanced; and
- resources are shared fairly.

The restaurant example shows how CSP can be applied to a realistic system that
combines concurrency, resource management, communication, and error handling in
one framework.

---

## End-of-Chapter Exercises

**Submission rules when using AI**

- Treat AI output as a proposal; the final judgment must come from a verifier.
- Submit the prompt used, the generated specification and invariants, the
  verification commands and logs (including seed, depth, and scope), and the
  repair history if a counterexample was found.
- For detailed templates, see Appendix D and Appendix F.

### Basic Exercise 1: Reading CSP Notation

Read the following CSP process definitions and explain the behavior of the
system.

【擬似記法】
```csp
PRODUCER = produce → buffer!item → PRODUCER
CONSUMER = buffer?x → consume.x → CONSUMER
BUFFER = in?x → out!x → BUFFER

SYSTEM = PRODUCER [| {buffer} |] BUFFER[buffer/in, buffer/out] [| {buffer} |] CONSUMER
```

Explain:

1. the role and behavior of each process;
2. the synchronization points among the processes;
3. the data flow through the whole system; and
4. an example of a possible execution sequence.

### Basic Exercise 2: Deadlock Analysis

Analyze whether the following system can deadlock.

【擬似記法】
```csp
PROCESS_A = resource1.acquire → resource2.acquire →
           work → resource2.release → resource1.release → PROCESS_A

PROCESS_B = resource2.acquire → resource1.acquire →
           work → resource1.release → resource2.release → PROCESS_B

SYSTEM = PROCESS_A [| {resource1.acquire, resource1.release,
                     resource2.acquire, resource2.release} |] PROCESS_B
```

Discuss:

1. a deadlock scenario;
2. the four deadlock conditions and whether they hold;
3. at least two prevention strategies; and
4. a corrected CSP definition.

### Practical Exercise 1: Designing an ATM System

Model an ATM system in CSP satisfying the following requirements.

**Basic functions**:

- card insertion and PIN entry;
- balance inquiry, withdrawal, and deposit; and
- receipt printing and card ejection.

**Concurrency requirements**:

- multiple ATMs access the same banking system;
- each ATM serves at most one customer at a time; and
- access to the central banking system must be controlled safely.

**Safety requirements**:

- prevent unauthorized access;
- reject withdrawals when funds are insufficient; and
- stop safely under network failure.

Tasks:

1. define the main processes;
2. define the resource-management mechanism;
3. integrate error handling; and
4. compose the whole system.

### Practical Exercise 2: Using Process Composition

For the ATM system above, extend the design in the following ways.

1. **Hierarchical design**
   - build composite operations from basic operations;
   - separate the interface layer from the business-logic layer.
2. **Concurrency control**
   - support concurrent use by multiple customers at different ATMs;
   - add a maintenance mode for administrators.
3. **Communication patterns**
   - introduce reliable communication between ATMs and the central system;
   - add failure detection and recovery.

### Advanced Exercise: Designing a Distributed System

Design a distributed file system in CSP.

**System structure**:

- multiple client nodes;
- multiple storage nodes; and
- redundant metadata servers.

**Requirements**:

- file read and write operations;
- data redundancy through replication;
- tolerance to node failures; and
- consistency guarantees.

**Design tasks**:

1. inter-node communication protocol;
2. failure detection and recovery;
3. distributed agreement algorithm; and
4. load-balancing mechanism.

**Properties to verify**:

- absence of deadlock;
- preservation of data consistency;
- robustness under partial failure; and
- fairness, meaning that every client eventually receives service.

Through these exercises, you should acquire practical skill in designing
concurrent systems with CSP and be prepared for the richer treatment of
temporal properties in the next chapter.
