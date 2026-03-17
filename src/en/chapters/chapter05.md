# Chapter 5: State-Based Specification: Foundations of Z Notation

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter05.md`

## 5.1 The World of Z Notation: Thinking in Terms of State and Schemas

### A Culture of Precision Born in Oxford

Z notation was developed at the Oxford University Computing Laboratory from the
late 1970s into the 1980s. The background was a growing recognition that
software systems were becoming too complex for informal methods to guarantee
quality reliably.

The creators of Z tried to address this problem by importing mathematical
rigor into software specification. Their goal, however, was not merely to write
software documents with mathematical symbols. They wanted a practical form of
mathematical rigor that software engineers could actually use.

The result was Z notation, which is often described as "readable mathematics."
Complex mathematical ideas are expressed in a structured way, making them
usable not only by mathematicians but also by practitioners who need to design
and review software systems.

### A State-Centered Worldview

The defining feature of Z notation is its state-centered worldview. A system is
understood as a combination of state and operations that transform that state.
This viewpoint is close to database design and state-machine thinking.

When we think in state-centered terms, we first identify the information the
system must carry, namely its state variables. Next, we define invariants over
those variables. Only then do we describe the operations that change the state.
That order matters. It is impossible to discuss whether an operation is correct
unless the valid states of the system are already understood.

Consider a library system. A conventional object-oriented approach may start
from a `Book` object or a `Member` object. Z begins elsewhere: what is the
state of the library? Which books exist, which are on loan, and who has
borrowed which book? Those pieces of information and their relations define the
system state.

### The Structured Wisdom of Schemas

One of the most innovative ideas in Z notation is the *schema*. A schema is a
way to package related declarations and constraints together. This is not just
a notational convenience. It is a deep mechanism for managing complexity.

![Figure 5-1: Schema structure in Z notation and state-based specification]({{ '/assets/images/diagrams/z-notation-schema-structure.svg' | relative_url }})

Human cognitive capacity is limited. A software system may contain dozens or
hundreds of relevant elements, but a person cannot reason about all of them at
once. Schemas are an abstraction mechanism for overcoming that limit.

By grouping related variables and constraints into one conceptually coherent
unit, a schema lets us break a large system into understandable pieces. Schemas
are also reusable, so recurring structures can be captured once and then
included elsewhere.

### Putting Mathematical Foundations to Work

Z notation is built on established mathematical foundations such as set theory,
logic, and functions. It does not simply reproduce those subjects verbatim. It
adapts them into a practical notation for software specification.

For example, the mathematical idea of a function is refined into several
categories that matter directly in software: partial functions, total
functions, injections, and so on. Each of these captures a different aspect of
system structure or behavior.

Z also places strong emphasis on types. This is reminiscent of type systems in
programming languages, but Z is often more expressive. Types help detect
mistakes early and make a specification easier to understand.

### Industrial Successes and Lessons Learned

Z notation has a long record not only in academic work but also in industry,
especially in safety-critical domains such as transportation control, aerospace
systems, and nuclear applications.

One major lesson from these cases is the importance of gradual adoption. It is
usually ineffective to rewrite an entire system specification in Z at once. A
better approach is to begin with the most critical part of the system and then
expand the scope step by step.

Another lesson is that Z succeeds only when a team develops a shared
understanding of how to use it. Learning the notation is necessary, but not
sufficient. The team also has to build a culture in which the notation supports
review and communication.

## 5.2 The System of Mathematical Notation: Making Sets and Logic Practical

### Symbols as a Common Language

The greatest value of mathematical notation is uniqueness of interpretation.
Natural language makes expressions such as "large," "small," "many," or "few"
ambiguous. Symbols such as `≤`, `≥`, `∈`, and `⊆` have stable meanings
independent of language and region.

Z notation builds a software-oriented notation on top of that stability. The
important thing is not memorizing symbols mechanically, but understanding the
concept each symbol captures.

### Basic Types and Constructed Types

In Z, we begin by defining basic types and then combine them to construct more
elaborate types.

**Examples of basic types**:

【ツール準拠（そのまま動く）】
```z
[Person, BookID, Date]
```

Names in square brackets denote basic types. Each one represents a set of
primitive elements that we do not decompose any further.

**Examples of constructed types**:

【ツール準拠（そのまま動く）】
```z
Name == seq Char
Status ::= available | borrowed | reserved
Address == [street: seq Char; city: seq Char; zipcode: Nat]
```

Constructors such as sequences, free types, and record types allow us to build
new types from simpler ones.

### Practical Use of Set Operations

Set-theoretic operators are natural and powerful in software specification.

**Basic set operators**:

- `∈` (membership)
- `⊆` (subset)
- `∪` (union)
- `∩` (intersection)
- `\` (difference)
- `ℙ` (power set)

**Practical example: library stock management**

【ツール準拠（そのまま動く）】
```z
availableBooks == allBooks \ borrowedBooks
overdueBooks == {b: borrowedBooks | dueDate(b) < today}
popularBooks == {b: allBooks | #borrowers(b) > threshold}
```

Such expressions are far more precise than natural language, and often more
readable than code.

### The Hierarchy of Relations and Functions

Z notation distinguishes clearly between general relations and the various
special cases of functions.

**Basic relation and function symbols used in this chapter**

- `X ↔ Y`: an arbitrary binary relation
- `X ⇸ Y`: a partial function
- `X → Y`: a total function
- `X ↣ Y`: an injection
- `x ↦ y`: a maplet, that is, an explicit pair

**Practical example: student enrollment**

【擬似記法】
```z
enrollment: Student ↔ Course
advisor: Student ⇸ Teacher
teaches: Teacher → ℙ Course
studentID: Student ↣ StudentNumber
```

The enrollment relation is many-to-many. An advisor is modeled as a partial
function because some students may not yet have an advisor. `teaches` is a
total function to sets of courses, and `studentID` is injective because student
numbers must be unique.

### Practical Use of Predicate Logic

Quantifiers such as `∀` and `∃` are central in specification writing.

**Universal quantification**:

【擬似記法】
```z
∀ s: Student • #(s.courses) ≤ maxCourses

∀ b: BorrowedBook • b.dueDate ≥ b.borrowDate + 14
```

The first formula states that every student is under the enrollment limit. The
second states that every borrowed book has a due date at least fourteen days
after its borrowing date.

**Existential quantification**:

【擬似記法】
```z
∃ a: Admin • a.isActive = true

∃! p: Person • p.email = targetEmail
```

The first says that at least one active administrator exists. The second says
that exactly one person has the target email address.

### Integrating Notation Inside a Schema

The real strength of Z appears when these mathematical building blocks are
combined inside a schema.

【擬似記法】
```z
LibrarySystem
├─ books: ℙ Book
├─ members: ℙ Member
├─ loans: Member ↔ Book
├─ dueDate: Book ⇸ Date
├─────────────────────────
├─ dom loans ⊆ members
├─ ran loans ⊆ books
├─ ran loans ⊆ dom dueDate
├─ ∀ m: Member • #(loans[{m}]) ≤ maxLoans
└─ ∀ b: ran loans • dueDate(b) > today
```

This schema gives a mathematically precise description of library state, while
remaining readable at the design level.

### Reading and Pronouncing the Notation

To use Z effectively in practice, a team must be able to read the symbols
correctly. This matters for discussion and review.

**Typical readings**:

- `x ∈ S`: "x belongs to S" or "x is in S"
- `A ⊆ B`: "A is a subset of B"
- `f: X → Y`: "f is a function from X to Y"
- `∀ x: X • P(x)`: "for all x in X, P of x"
- `∃ x: X • P(x)`: "there exists x in X such that P of x"

Once the team shares a consistent way of reading the notation, Z becomes much
more practical as a communication medium.

## 5.3 Describing State with Schemas

### The Fundamental Idea of Structured State

To understand the state of a complex system, some kind of structure is
essential. Schemas in Z provide that structure. They do more than group
variables. They also collect the constraints that maintain consistency.

This makes it possible to answer a fundamental design question precisely: what
counts as a valid state of the system?

### The Basic Structure of a Schema

A Z schema consists of a declaration part and a predicate part. The declaration
part introduces state variables and their types. The predicate part states the
relationships and constraints among them.

【擬似記法】
```z
┌─ BankAccount ─────────────────────┐
│ accountNumber: AccountID          │
│ balance: ℕ                        │
│ owner: Person                     │
│ isActive: 𝔹                       │
├───────────────────────────────────┤
│ balance ≤ creditLimit             │
│ isActive ⇒ owner ∈ validCustomers │
└───────────────────────────────────┘
```

The upper part is the declaration part. The lower part contains invariants that
must always hold.

### Representing Composite State

Real systems usually contain several interrelated collections and mappings.
Schemas can express those compound structures naturally.

【擬似記法】
```z
┌─ Library ─────────────────────────┐
│ books: ℙ Book                     │
│ members: ℙ Member                 │
│ catalogue: Book → BookInfo        │
│ loans: Member ↔ Book              │
│ reservations: Member ↔ Book       │
├───────────────────────────────────┤
│ dom catalogue = books             │
│ dom loans ⊆ members               │
│ ran loans ⊆ books                 │
│ ∀ m: Member • #(loans[{m}]) ≤ 5   │
│ loans ∩ reservations = ∅          │
└───────────────────────────────────┘
```

This schema captures a realistic library state. Each constraint represents a
piece of the system's integrity policy.

### Hierarchical Schema Design

Large systems benefit from hierarchical structuring. Lower-level schemas can be
combined into higher-level ones.

【擬似記法】
```z
┌─ PersonalInfo ───────────────────┐
│ name: Name                       │
│ address: Address                 │
│ phoneNumber: PhoneNumber         │
├─────────────────────────────────┤
│ name ≠ ""                        │
│ isValidPhone(phoneNumber)        │
└─────────────────────────────────┘

┌─ BankingInfo ────────────────────┐
│ accountNumbers: ℙ AccountID      │
│ creditRating: CreditRating       │
│ lastTransaction: Date            │
├─────────────────────────────────┤
│ #accountNumbers ≥ 1              │
│ creditRating ∈ {A, B, C, D, E}   │
└─────────────────────────────────┘

┌─ Customer ───────────────────────┐
│ PersonalInfo                     │
│ BankingInfo                      │
├─────────────────────────────────┤
│ lastTransaction ≤ today          │
└─────────────────────────────────┘
```

Hierarchical organization preserves local clarity while controlling overall
complexity.

### Expressing State Invariants

State invariants are among the most important elements of a Z specification.
They capture the consistency properties that must survive every operation.

【擬似記法】
```z
┌─ OnlineStore ────────────────────┐
│ products: ℙ Product              │
│ inventory: Product → ℕ           │
│ orders: ℙ Order                  │
│ orderItems: Order → ℙ Product    │
│ reservedStock: Product → ℕ       │
├─────────────────────────────────┤
│ dom inventory = products         │
│ dom reservedStock = products     │
│ ∀ p: Product •                   │
│   reservedStock(p) ≤ inventory(p)│
│ ∀ o: orders; p: orderItems(o) •  │
│   p ∈ products                   │
└─────────────────────────────────┘
```

These invariants encode the core of the business logic, such as inventory
consistency and order validity.

### Expressing Conditional State

System constraints often depend on conditions. Z can express such conditional
state restrictions naturally.

【擬似記法】
```z
┌─ FlightBookingSystem ────────────┐
│ flights: ℙ Flight                │
│ bookings: ℙ Booking              │
│ passengers: Booking → ℙ Passenger│
│ flightStatus: Flight → Status    │
│ capacity: Flight → ℕ             │
├─────────────────────────────────┤
│ ∀ f: flights •                   │
│   flightStatus(f) = cancelled ⇒  │
│     ¬∃ b: bookings • b.flight = f│
│ ∀ f: flights; b: bookings •      │
│   b.flight = f ⇒                 │
│     #(passengers(b)) ≤ capacity(f)│
│ ∀ b: bookings •                  │
│   b.isPaid ∨ b.paymentDue ≤ today│
└─────────────────────────────────┘
```

### Considering Time-Dependent State

In dynamic systems, state evolves over time. Z can model that dependence
explicitly when needed.

【擬似記法】
```z
┌─ TimedSystem ────────────────────┐
│ currentTime: Time                │
│ events: ℙ Event                  │
│ schedule: Event → Time           │
│ completed: ℙ Event               │
├─────────────────────────────────┤
│ completed ⊆ events               │
│ ∀ e: completed •                 │
│   schedule(e) ≤ currentTime      │
│ ∀ e: events \ completed •        │
│   schedule(e) > currentTime      │
└─────────────────────────────────┘
```

### Designing for Readability

Readable schemas are easier to review and maintain. The order of declarations,
the grouping of related constraints, and naming discipline all matter.

Useful principles include:

1. Place related variables together.
2. Write constraints in a logical order.
3. Use meaningful names.
4. Split complex constraints over multiple lines.

【擬似記法】
```z
┌─ WebServer ──────────────────────┐
│ // Connection management         │
│ activeConnections: ℙ Connection  │
│ maxConnections: ℕ                │
│                                  │
│ // Resource management           │
│ availableMemory: ℕ               │
│ usedMemory: ℕ                    │
│ totalMemory: ℕ                   │
├─────────────────────────────────┤
│ // Connection limit              │
│ #activeConnections ≤ maxConnections│
│                                  │
│ // Memory consistency            │
│ usedMemory + availableMemory = totalMemory│
│ usedMemory ≥ 0                   │
│ availableMemory ≥ 0              │
└─────────────────────────────────┘
```

Structured presentation makes the intention of the schema visible, not just the
raw formulas.

## 5.4 Operation Schemas: Describing State Change

### Operations as State Transformations

In Z notation, an operation is understood as a state transformation. It defines
the mathematical relation between a pre-state and a post-state. That viewpoint
makes it possible to reason rigorously about correctness and about how
operations interact.

An operation schema describes the current state, the next state, any inputs,
and any outputs. It makes explicit not only what the operation changes, but
also what it leaves unchanged.

### Delta Schemas and Xi Schemas

Z provides dedicated notation for operations.

**Delta notation (`Δ`)**: the operation changes state.

【擬似記法】
```z
ΔLibrary
≙ Library ∧ Library'
```

This means that both the pre-state `Library` and the post-state `Library'` are
in scope.

**Xi notation (`Ξ`)**: the operation does not change state.

【擬似記法】
```z
ΞLibrary
≙ ΔLibrary ∧ θLibrary = θLibrary'
```

It states that all bindings in the schema are preserved across the operation.

### A Detailed Borrow Operation

Let us examine a book-borrowing operation in a library system.

【擬似記法】
```z
┌─ BorrowBook ─────────────────────┐
│ ΔLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // Preconditions                 │
│ member? ∈ members                │
│ book? ∈ books                    │
│ book? ∉ ran loans                │
│ #(loans[{member?}]) < maxLoans   │
│                                  │
│ // Postconditions                │
│ loans' = loans ∪ {member? ↦ book?}│
│ books' = books                   │
│ members' = members               │
│ result! = success                │
└─────────────────────────────────┘
```

Input variables are marked with `?` and outputs with `!`. The schema states
both the conditions required for normal execution and the resulting next state.

### Formalizing Error Handling

Real systems must define error behavior as carefully as success behavior. Z can
capture both in the same overall framework.

【擬似記法】
```z
┌─ BorrowBookError ────────────────┐
│ ΞLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ member? ∉ members ∨              │
│ book? ∉ books ∨                  │
│ book? ∈ ran loans ∨              │
│ #(loans[{member?}]) ≥ maxLoans   │
│                                  │
│ result! ∈ {memberNotFound,       │
│            bookNotFound,         │
│            alreadyBorrowed,      │
│            loanLimitExceeded}    │
└─────────────────────────────────┘
```

Because the schema uses `ΞLibrary`, the state remains unchanged in the error
case.

### A Complete Operation Definition

A complete operation combines the normal and error cases.

【擬似記法】
```z
CompleteBorrowBook ≙ BorrowBook ∨ BorrowBookError
```

This definition ensures that the operation has specified behavior for every
relevant input category.

### Structuring More Complex Operations

For more elaborate business logic, it is often helpful to describe the
operation in stages.

【擬似記法】
```z
┌─ ProcessPurchase ────────────────┐
│ ΔOnlineStore                     │
│ customer?: Customer              │
│ items?: ℙ Product                │
│ paymentInfo?: Payment            │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // Stage 1: stock validation     │
│ ∀ item: items? • item ∈ products │
│ ∀ item: items? •                 │
│   inventory(item) ≥ requested(item)│
│                                  │
│ // Stage 2: payment processing   │
│ ValidatePayment                  │
│ ProcessPayment                   │
│                                  │
│ // Stage 3: inventory update     │
│ ∀ item: items? •                 │
│   inventory'(item) =             │
│     inventory(item) - requested(item)│
│                                  │
│ // Stage 4: order recording      │
│ CreateOrder                      │
│                                  │
│ result! = orderConfirmed         │
└─────────────────────────────────┘
```

### Before-and-After Relationships

Operation schemas are especially valuable because they let us state exactly how
the pre-state and post-state are related.

【擬似記法】
```z
┌─ TransferFunds ──────────────────┐
│ ΔBankingSystem                   │
│ fromAccount?: AccountID          │
│ toAccount?: AccountID            │
│ amount?: ℕ                       │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // Preconditions                 │
│ fromAccount? ∈ accounts          │
│ toAccount? ∈ accounts            │
│ fromAccount? ≠ toAccount?        │
│ balance(fromAccount?) ≥ amount?  │
│                                  │
│ // State changes                 │
│ balance'(fromAccount?) =         │
│   balance(fromAccount?) - amount?│
│ balance'(toAccount?) =           │
│   balance(toAccount?) + amount?  │
│                                  │
│ // Unchanged part                │
│ ∀ acc: accounts \ {fromAccount?, toAccount?} •│
│   balance'(acc) = balance(acc)   │
│ accounts' = accounts             │
│                                  │
│ result! = transferComplete       │
└─────────────────────────────────┘
```

The explicit unchanged part is the response to the frame problem in this style
of specification.

### Composition and Order of Operations

When multiple operations are combined, their order and dependency have to be
made explicit.

【ツール準拠（そのまま動く）】
```z
BookReservationProcess ≙
  CheckAvailability ⨾
  ReserveBook ⨾
  NotifyMember ⨾
  UpdateCatalogue
```

The operator `⨾` denotes sequential composition.

### Conditional Operations

Operations can also branch based on conditions.

【擬似記法】
```z
┌─ ProcessReturn ──────────────────┐
│ ΔLibrary                         │
│ member?: Member                  │
│ book?: Book                      │
│ returnDate?: Date                │
│ fine!: ℕ                         │
├─────────────────────────────────┤
│ member? ↦ book? ∈ loans          │
│                                  │
│ returnDate? > dueDate(book?) ⇒   │
│   fine! = calculateFine(book?, returnDate?)│
│                                  │
│ returnDate? ≤ dueDate(book?) ⇒   │
│   fine! = 0                      │
│                                  │
│ loans' = loans \ {member? ↦ book?}│
│ members' = members               │
│ books' = books                   │
└─────────────────────────────────┘
```

This one schema covers both the on-time return case and the overdue case.

## 5.5 Schema Calculus: Building Complex Operations

### The Algebraic Structure of Operations

The deeper power of Z notation lies in its ability to compose simple
operations into more complex ones. This is analogous to algebra, where
operators can be combined to derive larger expressions.

That algebraic view improves reuse, supports layered design, and makes
relationships among operations mathematically analyzable.

### Schema Composition

The most basic schema-calculus operation is composition through logical
operators.

**Composition by conjunction (`∧`)**:

【擬似記法】
```z
AuthenticatedOperation ≙
  UserAuthentication ∧
  SystemOperation
```

This defines an operation that must satisfy both the authentication constraint
and the system-operation constraint.

**Composition by disjunction (`∨`)**:

【擬似記法】
```z
FlexiblePayment ≙
  CreditCardPayment ∨
  BankTransferPayment ∨
  DigitalWalletPayment
```

This schema allows one of several payment mechanisms.

### Sequential Composition

Many real operations consist of several stages executed in sequence.

【ツール準拠（そのまま動く）】
```z
CompleteBooking ≙
  ValidateRequest ⨾
  CheckAvailability ⨾
  ProcessPayment ⨾
  ConfirmReservation ⨾
  SendConfirmation
```

Each stage feeds into the next one, together forming a larger transaction.

### Expressing Conditional Branches

Conditional behavior can also be written in schema-calculus style.

【擬似記法】
```z
ProcessOrder ≙
  (InStock ∧ ImmediateDelivery) ∨
  (OutOfStock ∧ BackOrder) ∨
  (SpecialOrder ∧ CustomProcessing)
```

### Integrating Error Handling

Production systems need a clean integration of success and failure behavior.

【擬似記法】
```z
RobustOperation ≙
  (Preconditions ∧ NormalProcessing) ∨
  (¬Preconditions ∧ ErrorHandling)
```

A more concrete example:

【擬似記法】
```z
┌─ SafeWithdrawal ─────────────────┐
│ (ValidAccount ∧ SufficientFunds  │
│  ∧ WithinDailyLimit ∧ ProcessWithdrawal) │
│ ∨                                │
│ (¬ValidAccount ∧ AccountError)   │
│ ∨                                │
│ (¬SufficientFunds ∧ InsufficientFundsError)│
│ ∨                                │
│ (¬WithinDailyLimit ∧ LimitExceededError)│
└─────────────────────────────────┘
```

### Parallel Composition

Some operations conceptually run in parallel.

【ツール準拠（そのまま動く）】
```z
ParallelProcessing ≙
  DatabaseUpdate ∥
  CacheRefresh ∥
  LogEntry
```

The operator `∥` denotes parallel composition.

### Abstraction and Concretization

Schema calculus also supports a stepwise refinement from abstract to concrete
operations.

**Abstract level**:

【ツール準拠（そのまま動く）】
```z
PaymentProcess ≙
  ValidatePayment ⨾
  ProcessTransaction ⨾
  UpdateRecords
```

**More concrete level**:

【擬似記法】
```z
CreditCardPayment ≙
  (ValidateCreditCard ∧ CheckCreditLimit) ⨾
  (ContactPaymentGateway ∧ ProcessCreditTransaction) ⨾
  (UpdateAccountBalance ∧ RecordTransaction ∧ SendReceipt)
```

### Minimizing State Change

One response to the frame problem is to define the changed and unchanged parts
of the state explicitly.

【擬似記法】
```z
┌─ MinimalUpdate ──────────────────┐
│ ΔSystemState                     │
│ targetField?: FieldID            │
│ newValue?: Value                 │
├─────────────────────────────────┤
│ // Update only the target field  │
│ state'(targetField?) = newValue? │
│                                  │
│ // Everything else is unchanged  │
│ ∀ field: dom state \ {targetField?} •│
│   state'(field) = state(field)   │
└─────────────────────────────────┘
```

### Reversibility of Operations

In some domains, inverse operations such as undo are an essential design
concern.

【擬似記法】
```z
UndoableOperation ≙
  (DoAction ∧ SaveUndoInfo) ∨
  (UndoAction ∧ RestorePreviousState)

FileManagement ≙
  (DeleteFile ∧ MoveToTrash) ∨
  (RestoreFile ∧ MoveFromTrash)
```

### Integrating Access Control

Systems with security requirements often need an access-control wrapper around
all operations.

【擬似記法】
```z
SecureOperation[X] ≙
  AuthorizeUser ∧
  CheckPermissions ∧
  X ∧
  LogAccess
```

This generic pattern adds security control to an arbitrary operation `X`.

【ツール準拠（そのまま動く）】
```z
SecureFileAccess ≙ SecureOperation[ReadFile]
SecureDataModification ≙ SecureOperation[UpdateDatabase]
```

### Performance Characteristics of Operations

Schema calculus can also help document performance-related design choices.

【擬似記法】
```z
EfficientOperation ≙
  (SmallDataSet ∧ LinearSearch) ∨
  (LargeDataSet ∧ IndexedSearch)

OptimizedQuery ≙
  CacheCheck ⨾
  (CacheHit ∧ ReturnCachedResult) ∨
  (CacheMiss ∧ DatabaseQuery ∧ UpdateCache)
```

This kind of description does not replace measurement, but it makes the
assumed performance strategy explicit in the specification.

## 5.6 Applying the Method to the Real World: An Elevator Control System

### Analyzing the System Requirements

The elevator control system is a classic example for formal methods. It is
safety-critical, contains real-time and concurrent aspects, and exhibits
nontrivial state transitions. That makes it a strong example for Z notation.

Let us first summarize the main requirements.

**Functional requirements**:

- respond to passenger calls;
- determine an efficient movement schedule;
- stop at requested floors; and
- control door opening and closing.

**Safety requirements**:

- the elevator must not move while the doors are open;
- the cabin must not exceed capacity; and
- under mechanical failure, the system must stop in a safe condition.

**Performance requirements**:

- minimize average waiting time; and
- optimize energy efficiency.

### The Basic State Model

We can model the system state in stages.

**Basic type definitions**:

【ツール準拠（そのまま動く）】
```z
[FloorNumber, PassengerID, Time]

Direction ::= up | down | stationary
DoorState ::= open | closed | opening | closing
ElevatorState ::= moving | stopped | maintenance
```

**Basic state schema**:

【擬似記法】
```z
┌─ ElevatorStatus ─────────────────┐
│ currentFloor: FloorNumber        │
│ direction: Direction             │
│ doorState: DoorState             │
│ elevatorState: ElevatorState     │
│ passengers: ℙ PassengerID        │
│ capacity: ℕ                      │
├─────────────────────────────────┤
│ #passengers ≤ capacity           │
│ elevatorState = moving ⇒         │
│   doorState = closed             │
│ doorState ∈ {open, opening} ⇒    │
│   elevatorState = stopped        │
└─────────────────────────────────┘
```

### The Call-Management Subsystem

Handling hall calls and cabin calls is one of the central functions.

【擬似記法】
```z
┌─ CallSystem ─────────────────────┐
│ upCalls: ℙ FloorNumber           │
│ downCalls: ℙ FloorNumber         │
│ cabinCalls: ℙ FloorNumber        │
│ minFloor: FloorNumber            │
│ maxFloor: FloorNumber            │
├─────────────────────────────────┤
│ upCalls ⊆ minFloor .. maxFloor-1 │
│ downCalls ⊆ minFloor+1 .. maxFloor│
│ cabinCalls ⊆ minFloor .. maxFloor│
│ minFloor < maxFloor              │
└─────────────────────────────────┘
```

### Integrated System State

The overall system state includes both the elevator's physical status and the
call-management state.

【擬似記法】
```z
┌─ ElevatorSystem ─────────────────┐
│ ElevatorStatus                   │
│ CallSystem                       │
│ currentTime: Time                │
│ lastMaintenance: Time            │
│ totalTrips: ℕ                    │
├─────────────────────────────────┤
│ elevatorState = maintenance ⇒    │
│   passengers = ∅                 │
│ currentFloor ∈ minFloor .. maxFloor│
│ lastMaintenance ≤ currentTime    │
└─────────────────────────────────┘
```

### A Basic Operation: Registering a Hall Call

We next define an operation that records an external call.

【擬似記法】
```z
┌─ RegisterUpCall ─────────────────┐
│ ΔElevatorSystem                  │
│ floor?: FloorNumber              │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ floor? ∈ minFloor .. maxFloor-1  │
│ elevatorState ≠ maintenance      │
│                                  │
│ upCalls' = upCalls ∪ {floor?}    │
│ downCalls' = downCalls           │
│ cabinCalls' = cabinCalls         │
│ ΞElevatorStatus                  │
│                                  │
│ result! = callRegistered         │
└─────────────────────────────────┘
```

The same style can be used for downward hall calls and cabin calls.

### A More Complex Operation: Scheduling

The scheduler is the more intelligent part of the system. It decides the next
target floor based on current requests and current direction.

【擬似記法】
```z
┌─ DetermineNextFloor ─────────────┐
│ ΞElevatorSystem                  │
│ nextFloor!: FloorNumber          │
│ newDirection!: Direction         │
├─────────────────────────────────┤
│ elevatorState = stopped          │
│ upCalls ∪ downCalls ∪ cabinCalls ≠ ∅│
│                                  │
│ // Highest-priority floor in the current direction│
│ direction = up ⇒                 │
│   nextFloor! = min({f: upCalls ∪ cabinCalls │
│                    | f > currentFloor})     │
│                                  │
│ direction = down ⇒               │
│   nextFloor! = max({f: downCalls ∪ cabinCalls│
│                    | f < currentFloor})      │
│                                  │
│ direction = stationary ⇒         │
│   nextFloor! = min({f: upCalls ∪ downCalls ∪│
│                         cabinCalls │         │
│                    | f ≠ currentFloor})     │
│                                  │
│ nextFloor! > currentFloor ⇒ newDirection! = up│
│ nextFloor! < currentFloor ⇒ newDirection! = down│
│ nextFloor! = currentFloor ⇒ newDirection! = stationary│
└─────────────────────────────────┘
```

### A Safety-Critical Operation: Door Control

Door control directly affects safety, so the preconditions are especially
important.

【擬似記法】
```z
┌─ OpenDoor ───────────────────────┐
│ ΔElevatorSystem                  │
│ result!: RESPONSE                │
├─────────────────────────────────┤
│ // Safety preconditions          │
│ elevatorState = stopped          │
│ direction = stationary           │
│ doorState = closed               │
│                                  │
│ // There is a request at the current floor│
│ currentFloor ∈ upCalls ∪ downCalls ∪ cabinCalls│
│                                  │
│ // State update                  │
│ doorState' = opening             │
│ elevatorState' = elevatorState   │
│ currentFloor' = currentFloor     │
│ direction' = direction           │
│ passengers' = passengers         │
│                                  │
│ // Clear the served calls        │
│ upCalls' = upCalls \ {currentFloor}│
│ downCalls' = downCalls \ {currentFloor}│
│ cabinCalls' = cabinCalls \ {currentFloor}│
│                                  │
│ result! = doorOpening            │
└─────────────────────────────────┘
```

### Emergency Operations

In a safety-critical system, emergency behavior must also be specified
explicitly.

【擬似記法】
```z
┌─ EmergencyStop ──────────────────┐
│ ΔElevatorSystem                  │
│ reason?: EmergencyReason         │
├─────────────────────────────────┤
│ reason? ∈ {fire, earthquake,     │
│            powerFailure, mechanical}│
│                                  │
│ // Stop immediately              │
│ elevatorState' = maintenance     │
│ direction' = stationary          │
│                                  │
│ // Door control under emergency  │
│ reason? = fire ⇒ doorState' = open│
│ reason? ≠ fire ⇒ doorState' = closed│
│                                  │
│ // Clear pending calls           │
│ upCalls' = ∅                     │
│ downCalls' = ∅                   │
│ cabinCalls' = ∅                  │
│                                  │
│ // Preserve other parts          │
│ currentFloor' = currentFloor     │
│ passengers' = passengers         │
└─────────────────────────────────┘
```

### Verifying System-Level Properties

Once the model is complete enough, we can state important system properties.

**Safety property**:

【擬似記法】
```z
SafetyInvariant ≙
  ∀ ElevatorSystem •
    (doorState ∈ {open, opening} ⇒ elevatorState = stopped) ∧
    (#passengers ≤ capacity) ∧
    (elevatorState = moving ⇒ doorState = closed)
```

**Liveness property**:

【擬似記法】
```z
LivenessProperty ≙
  ∀ ElevatorSystem •
    (upCalls ∪ downCalls ∪ cabinCalls ≠ ∅) ⇒
    ∃ ElevatorSystem' •
      (upCalls' ∪ downCalls' ∪ cabinCalls') ⊂
      (upCalls ∪ downCalls ∪ cabinCalls)
```

The liveness property expresses that if there are pending calls, eventually the
set of pending calls becomes smaller.

### Formalizing Performance Characteristics

Formal specification can also record performance expectations.

【擬似記法】
```z
┌─ PerformanceMetrics ─────────────┐
│ averageWaitTime: ℝ               │
│ energyConsumption: ℝ             │
│ totalDistance: ℕ                 │
├─────────────────────────────────┤
│ averageWaitTime ≤ maxAcceptableWait│
│ energyConsumption ≤ energyBudget │
│ // Efficiency requirement        │
│ ∀ trip: TripSequence •           │
│   optimizeRoute(trip)            │
└─────────────────────────────────┘
```

This elevator example illustrates the main value of Z notation: safety,
functionality, and performance expectations can all be described in one unified
framework.

---

## End-of-Chapter Exercises

### Basic Exercise 1: Reading and Analyzing a Schema

Read the following Z schema and explain the system structure and constraints it
represents.

【擬似記法】
```z
┌─ UniversityDatabase ─────────────┐
│ students: ℙ Student              │
│ courses: ℙ Course                │
│ lecturers: ℙ Lecturer            │
│ enrollment: Student ↔ Course     │
│ teaching: Lecturer ↔ Course      │
│ grades: Student ⤇ Course → Grade │
├─────────────────────────────────┤
│ dom enrollment ⊆ students        │
│ ran enrollment ⊆ courses         │
│ dom teaching ⊆ lecturers         │
│ ran teaching ⊆ courses           │
│ ∀ c: courses • ∃ l: lecturers •  │
│   l ↦ c ∈ teaching               │
│ dom(dom grades) ⊆ students       │
│ ran(dom grades) ⊆ courses        │
└─────────────────────────────────┘
```

Explain:

1. The meaning and type of each variable
2. The meaning and plausibility of each constraint
3. Examples of situations that this model can express
4. Requirements that this model might still fail to express

### Basic Exercise 2: Writing an Operation Schema

For the university system above, create an operation schema for student course
registration.

**Student registration operation**

- A student registers for a new course.
- Preconditions: the student exists, the course exists, and the student is not
  already enrolled.
- Postcondition: the enrollment relation is extended.
- Error cases: unknown student, unknown course, duplicate enrollment.

Produce:

1. the normal-case operation schema;
2. the error-case operation schema; and
3. the complete operation definition combining both.

### Practical Exercise 1: Modeling a Banking System

Model a banking system in Z notation that satisfies the following requirements.

**Basic elements**:

- customers (name, address, phone number);
- accounts (account number, balance, type, owner); and
- transactions (transaction ID, account, amount, timestamp, type).

**Constraints**:

- account balances are non-negative;
- every account has an owner;
- transactions apply only to existing accounts; and
- account numbers are unique.

**Operations**:

- opening an account;
- depositing money;
- withdrawing money; and
- transferring funds between accounts.

Tasks:

1. define the state schema;
2. define the operation schema for each operation; and
3. identify the key invariants.

### Practical Exercise 2: Using Schema Calculus

For the banking system from the previous exercise, use schema calculus to
achieve the following goals.

1. **Define secure operations**
   - add authentication checks to every operation;
   - automate logging.
2. **Integrate error handling**
   - combine normal and error cases consistently;
   - define a uniform error response style.
3. **Represent transaction atomicity**
   - express transfer as a composition of withdrawal and deposit;
   - handle rollback when an error occurs midway.

### Advanced Exercise: Specifying a Real-Time System

Model a traffic-signal control system with a notion of time using Z notation.

**Requirements**:

- a four-way intersection (north-south and east-west);
- vehicle signals and pedestrian signals for each direction;
- safety: conflicting directions must not be green at the same time;
- efficiency: minimum green-time and maximum red-time constraints; and
- pedestrian requests through push buttons.

**Elements to model**:

1. signal states (red, yellow, green);
2. time concepts (timers and current time);
3. vehicle-detection sensors;
4. pedestrian request buttons; and
5. signal-change operations.

**Properties to verify**:

1. **Safety**: unsafe signal combinations never occur.
2. **Liveness**: every direction eventually receives a green signal.
3. **Fairness**: no direction waits indefinitely.

Through these exercises, you should acquire practical skill in system modeling
with Z notation and be ready for the process-centered descriptions in the next
chapter.
