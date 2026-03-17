---
layout: book
title: "Chapter 2: Bridging Mathematics and Programs"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter02.md"
---
# Chapter 2: Bridging Mathematics and Programs

## 2.1 The Mathematical Structure Hidden in Programming

Many people say, "I am not good at mathematics, but I like programming." Yet
programming itself is already deeply mathematical. When you declare variables,
define functions, write conditionals, or construct loops, you are already using
mathematical ideas, whether you notice it or not.

Realizing that fact is one of the first steps toward formal methods. Formal
methods are not a completely foreign world. They extend ideas that programmers
already use and make them more explicit and more rigorous.

This chapter clarifies the correspondence between basic programming concepts and
their mathematical counterparts. The goal is to build a natural bridge to the
formal specification techniques introduced from Chapter 3 onward. In
particular, the mathematical foundations used in Alloy, Z notation, CSP, and
TLA+ are introduced through concepts that should already be familiar from
ordinary programming. To provide a high-level view of the methods discussed in
this book, the chapter also refers to a comparison matrix of representative
formal techniques (Figure 2-2).

![Figure 2-1: Correspondence between programming concepts and mathematical concepts]({{ '/assets/images/diagrams/programming-math-correspondence.svg' | relative_url }})

![Figure 2-2: Comparison matrix of major formal methods]({{ '/assets/images/diagrams/formal-methods-comparison-matrix.svg' | relative_url }})

### Variables as Mathematical Objects with Names

One of the first concepts most programmers learn is the variable. But why is it
called a variable? What is the relationship between the `x` and `y` in the
equation `y = 2x + 1` and the `count` in `int count = 0`?

At a deeper level, both are instances of the same mathematical idea. Just as a
mathematical variable ranges over a set of possible values, a program variable
also ranges over a set of values. A variable of type `int` ranges over the set
of integers, while a variable of type `boolean` ranges over the two-element set
`{true, false}`.

If we push this idea further, program execution itself can be understood as the
process of assigning values to variables over time. If the value of a variable
`x` at time `t` is written as `x(t)`, then execution can be described as a
function over time.

That viewpoint becomes a foundation for Chapter 7, where TLA+ represents system
states as tuples of variable values and treats state change as a temporal
structure. It also supports the techniques in Chapter 10, where the evolution
of variable values is tracked mathematically in order to prove program
correctness.

### Functions: Abstraction of the Relationship Between Input and Output

Program functions and mathematical functions are, at their core, the same kind
of object. They accept inputs, perform a transformation, and produce outputs.
The mathematical function `f(x) = x²` and the program function
`square(x) { return x * x; }` use different notation, but they express the same
idea.

Programming functions, however, often have something mathematics usually hides:
side effects. A function may write to a file, update a screen, modify shared
state, or trigger communication with another system. Even these side effects
can be described mathematically if we view a function as an operation that
transforms system state.

This perspective becomes central in Chapter 5 on Z notation, where operations
are described rigorously as transformations from a pre-state to a post-state.
It also appears again in Chapter 10, where Hoare logic expresses the
correctness of state-changing programs by means of preconditions and
postconditions.

### Control Structures as Embodied Logic

Control structures such as conditionals and loops are embodiments of logical
concepts. A conditional corresponds to implication, while looping is closely
related to recursive definition and mathematical induction.

Consider the following simple conditional:

Pseudo notation:

```text
if (age >= 18) {
    status = "adult";
} else {
    status = "minor";
}
```

In logical terms, the same idea can be expressed as: "If the age is at least
18, the status is adult; otherwise the status is minor."

In mathematical notation, this becomes:
`status = (age ≥ 18) ? "adult" : "minor"`

Loops are more complex, but they can also be described mathematically. A
`for` loop corresponds to a sequence or indexed definition, while a `while`
loop can be understood as an iterative search constrained by a logical
condition.

### Data Structures as Implementations of Sets and Relations

Arrays, lists, dictionaries, and graphs are all implementations of mathematical
structures. Arrays can be viewed as ordered collections, dictionaries as
functions from keys to values, and graphs as explicit representations of
relations.

The array `[1, 3, 5, 7, 9]`, for example, can be understood as a function from
the index set `{0, 1, 2, 3, 4}` to the value set `{1, 3, 5, 7, 9}`. That is,
it represents a function such as `f(0) = 1`, `f(1) = 3`, and so on.

Associative arrays make this interpretation even clearer. The structure
`{"name": "Alice", "age": 30}` is a function from the key set
`{"name", "age"}` to a set of values.

These ideas become central in Chapter 4, where Alloy represents all data using
sets and relations. They also reappear in Chapter 5, where states can be
understood as mappings from variable names to values and where set-theoretic
operations become practical specification tools.

### Type Systems as Practical Applications of Set Theory

The type system of a programming language is a practical application of set
theory. A type defines a set of values, and type checking confirms whether a
value belongs to the set expected by an operation.

An `int` type denotes the set of integers; a `string` type denotes the set of
strings. Type safety is the guarantee that only values from the correct set are
passed where they are expected. Mathematically, this is the clarification of
the domain of a function.

More advanced type systems such as generics, algebraic data types, and
dependent types go further. They show how close programming can move toward
explicit mathematical structure.

### Error Handling as Mathematical Description of Exceptional Cases

Error handling and exceptions can also be described mathematically. If the
result of a function is modeled as "either a normal value or an exceptional
case," then errors become part of the function's formal behavior.

Consider a function `divide(a, b)`. It is not defined when `b = 0`.
Mathematically, the domain of the function is the set of input pairs `(a, b)`
for which `b ≠ 0`. A division-by-zero exception in a program corresponds to an
attempt to apply the function outside its domain.

## 2.2 Expressing Correctness Mathematically

### From Intuitive Correctness to Formal Correctness

Programmers constantly try to write correct programs. But what exactly does
"correct" mean? Does it mean that the code compiles? That it behaves as
expected? That it contains no bugs? Formal methods begin by sharpening such
intuitive notions into a mathematically precise concept of correctness.

At its core, program correctness is a relationship between specification and
implementation. The specification defines what a program is supposed to do; the
implementation defines what it actually does. Correctness is the correspondence
between the two.

### A Specification as a Promise

A useful analogy is a cooking recipe. A recipe specifies ingredients, steps,
and an expected result. Instructions such as "saute the onions until golden"
and "cook over high heat for three minutes" are already attempts at precise
specification.

Program specifications work in the same way. A statement such as "accept a
username and password as input, and return `true` if authentication succeeds
and `false` otherwise" specifies inputs, outputs, and intended behavior.

Yet natural-language specifications, like recipes, are ambiguous. What exactly
counts as "golden"? Under what exact conditions does "authentication succeed"?
Natural language is useful, but it leaves room for interpretation.

### The Power of Mathematical Specification

A mathematical specification removes that ambiguity. For an authentication
function, one possible specification is:

Pseudo notation:

```text
authenticate: String × String → Boolean
Precondition: username and password are non-empty strings
Postcondition:
  - if (username, password) is a valid combination, the result is true
  - otherwise, the result is false
  - the contents of the database are unchanged
```

This is far more explicit than a purely informal description. It makes the type
of the function clear, identifies the precondition, and states the guarantees
the function must satisfy.

### Correspondence with the Implementation

Implementation means writing code that satisfies the specification. But what
does "satisfies" mean? In formal methods, this is the notion of conformance.

An implementation conforms to a specification if, mathematically speaking, the
following conditions hold:

1. for every input that satisfies the precondition, the implementation
   terminates;
2. the output satisfies the postcondition; and
3. the implementation does not produce any side effects that the specification
   forbids.

This definition may sound abstract, but it is concrete enough to be verified.

### Partial Correctness and Total Correctness

There are two major aspects of correctness: partial correctness and total
correctness.

Partial correctness means that if the program terminates, the result is
correct. It does not rule out the possibility of an infinite loop or a crash.

Total correctness strengthens this by adding termination: the program must both
terminate and produce a correct result.

Consider the following function:

Pseudo notation:

```text
function factorial(n) {
    if (n <= 1) return 1;
    return n * factorial(n - 1);
}
```

Its partial correctness says that, when `n` is a natural number, the result is
`n!`. Total correctness additionally requires proof that the function always
terminates for such inputs.

### Invariants as Promises About the System

Another key concept is the invariant. An invariant is a property that must hold
throughout execution.

In a banking system, for example, a useful invariant might be: "the sum of all
account balances is equal to total deposits minus total withdrawals." No matter
which valid operations occur, that property should remain true.

Invariants capture system consistency. Database integrity constraints, class
invariants in object-oriented programming, and synchronization conditions in
concurrent systems are all examples of invariants.

### The Hierarchical Nature of Specifications

In real systems, specifications are hierarchical. There is a specification for
the whole system, specifications for individual modules, and specifications for
functions or operations.

This hierarchy is essential for managing complexity. By choosing appropriate
levels of abstraction, we can reason about large systems in a human-manageable
way. Formal methods provide techniques for writing and proving such layered
specifications rigorously.

## 2.3 Set Theory: A Language for Describing the World of Programs

### The Essence of Data: Collections of Elements

Data in programs is, at its essence, a collection of elements. Integers,
strings, records, and objects are all elements of some set. Set theory gives us
the mathematical language for talking about such collections precisely.

Its basic concepts are intuitive. A set is a collection, and an element is a
member of that collection. In programming terms, a type corresponds naturally
to a set, and a value corresponds to an element. The type `int` is the set of
integers; `boolean` is the two-element set `{true, false}`.

### Set Operations as Mathematical Descriptions of Data Manipulation

Many common data operations can be understood as set operations. Union,
intersection, and difference correspond to familiar program behavior such as
combining collections, filtering them, or removing elements.

Suppose we have two user groups:

- administrators: `{Alice, Bob, Charlie}`
- developers: `{Bob, David, Eve}`

Then:

- the union is "users who belong to either group":
  `{Alice, Bob, Charlie, David, Eve}`;
- the intersection is "users who belong to both groups": `{Bob}`;
- the difference is "administrators who are not developers":
  `{Alice, Charlie}`.

These are mathematical descriptions of operations such as list merging,
membership filtering, and query evaluation.

### Relations: Connections Between Elements

Another important set-theoretic concept is the relation. A relation expresses
which elements of one set are connected to elements of another.

Database tables provide a familiar example. The enrollment relation between the
set of students and the set of courses can be represented as a subset of the
Cartesian product of those two sets.

Pseudo notation:

```text
Students = {Alice, Bob, Charlie}
Courses = {Mathematics, Physics, Chemistry}
Enrollment = {
  (Alice, Mathematics),
  (Alice, Physics),
  (Bob, Mathematics),
  (Charlie, Chemistry)
}
```

### Functions as Special Relations

A function is a relation with an additional property: each input has exactly
one associated output. Program functions are implementations of that
mathematical idea.

Two important attributes of a function are its domain and codomain. The domain
is the set of inputs for which the function is defined. The codomain describes
the class of outputs it may produce. Many runtime errors can be understood as
attempts to apply a function outside its domain.

The square-root function `sqrt`, for example, has the nonnegative reals as its
ordinary domain. Applying it to a negative input produces a problem precisely
because the value lies outside that domain.

### Order Relations: Comparison and Sorting

Comparison is one of the most common operations in programming. Numerical
comparison, lexicographic ordering of strings, and temporal ordering of dates
are all examples of order relations.

An order relation defines how elements of a set can be compared. Mathematically
it is characterized by properties such as reflexivity (`a ≤ a`), antisymmetry
(`a ≤ b` and `b ≤ a` imply `a = b`), and transitivity (`a ≤ b` and `b ≤ c`
imply `a ≤ c`).

Sorting algorithms rely on such relations. To prove a sort correct, we must
confirm that the relation being used really behaves like an order.

### Cartesian Products: The Structure of Composite Data

Composite data types such as tuples, records, and structures can be described
mathematically as Cartesian products. If `A` and `B` are sets, the Cartesian
product `A × B` is the set of ordered pairs `(a, b)`.

For example, a coordinate type can be written as:

Pseudo notation:

```text
Point = {(x, y) | x ∈ Real, y ∈ Real}
```

This is the product `Real × Real`.

A slightly more complex example is user information:

Pseudo notation:

```text
User = Name × Age × Email
Name = String
Age = Natural
Email = String
```

In this way, composite program data can be described as products of simpler
types.

### Power Sets: The Set of Choices

The power set `P(A)` of a set `A` is the set of all subsets of `A`. This is
very useful in programming whenever we need to describe combinations of options
or permissions.

For example, if the basic permission set is `{read, write, execute}`, then the
possible permission combinations are elements of its power set:

Pseudo notation:

```text
P({read, write, execute}) = {
  {}, {read}, {write}, {execute},
  {read, write}, {read, execute}, {write, execute},
  {read, write, execute}
}
```

Bit flags, feature combinations, and configuration choices can all be
understood through this idea.

## 2.4 Logic: A Language for Talking About Program Properties

### Propositions: Sentences with Truth Values

Programming constantly involves judgment: "is the user authenticated?", "is the
index in range?", "does the file exist?" In logic, such statements are treated
as propositions.

A proposition is a sentence that has a truth value: true or false. Boolean
variables and conditional expressions in programs are concrete realizations of
propositions. Propositional logic provides the rules for combining them into
more complex conditions.

### Logical Operators: Combining Conditions

The operators AND (`&&`), OR (`||`), and NOT (`!`) are direct realizations of
logical operators.

- conjunction (AND): `P ∧ Q` is true exactly when both `P` and `Q` are true;
- disjunction (OR): `P ∨ Q` is true when at least one of `P` or `Q` is true;
- negation (NOT): `¬P` is true when `P` is false.

These operators are completely defined by truth tables. Complex conditions in
programs are built from these basic logical ingredients.

### Implication: Relationships Between Conditions

One of the most important ideas in program logic is implication. The statement
"if A, then B" is written `A → B`. It means that whenever `A` is true, `B` is
also true.

A conditional branch is a concrete implementation of implication:

Pseudo notation:

```text
if (user.isAuthenticated()) {
    return secretData;
}
```

This expresses the idea: "if the user is authenticated, then access to secret
data is permitted."

### Predicate Logic: A More Expressive Form of Logic

Propositional logic alone cannot express everything we need. Statements such
as "every user has a valid email address" or "there exists at least one
administrator" require quantifiers and therefore belong to predicate logic.

- universal quantifier (`∀`): "for all"
- existential quantifier (`∃`): "there exists"

Examples:

- `∀x ∈ Users. hasValidEmail(x)` means every user has a valid email address.
- `∃x ∈ Users. isAdmin(x)` means there exists at least one administrator.

Predicate logic becomes especially important in Chapter 3 and then reappears in
Alloy, Z notation, model checking, and theorem proving.

### Logic and Control Structures

Program control structures correspond closely to logical structure.

Conditional execution corresponds to implication:

Pseudo notation:

```text
if (condition) { action() }
≡ condition → action()
```

Loops can be related to quantified or repeated structure:

Pseudo notation:

```text
for (item in collection) { process(item) }
≡ ∀item ∈ collection. process(item)
```

Exception handling can be viewed as a logical decomposition of normal and error
cases:

Pseudo notation:

```text
try { normalAction() } catch { errorAction() }
≡ (normalAction() ∧ ¬error) ∨ (errorAction() ∧ error)
```

### Logical Inference: Proving Program Properties

Rules of logical inference form the basis of program proof. Two representative
examples are:

Modus ponens:

Pseudo notation:

```text
P → Q, P
---------
    Q
```

Hypothetical syllogism:

Pseudo notation:

```text
P → Q, Q → R
-------------
    P → R
```

Using such rules, we can prove more complex properties step by step.

### Logical Equivalence: Optimizing Conditions

Logical equivalence is useful when simplifying or optimizing conditions in
programs. De Morgan's laws, distributive laws, and associative laws all help
rewrite conditions into forms that are easier to understand or implement.

De Morgan's laws:

Pseudo notation:

```text
¬(P ∧ Q) ≡ (¬P ∨ ¬Q)
¬(P ∨ Q) ≡ (¬P ∧ ¬Q)
```

In program notation:

Pseudo notation:

```text
!(a && b) ≡ (!a || !b)
!(a || b) ≡ (!a && !b)
```

## 2.5 State and Change: Mathematical Modeling of Dynamic Systems

### The Deeper Idea of State

At a fundamental level, program execution is a succession of state changes.
Making the notion of state explicit is essential for understanding dynamic
systems.

The state of a system is a complete description of all information relevant to
its behavior at a given moment. In a program, that may include variable values,
memory contents, file-system state, network connections, and other factors that
affect behavior.

Mathematically, a state is represented as an element of a state space. The
state space `S` is the set of all possible states the system may assume.

### State Transitions: Mathematical Description of Change

Execution-driven state change can be represented as a state transition.
Mathematically, a transition can be modeled as a function on the state space.

A transition function `δ: S × I → S` takes a current state `s ∈ S` and an input
`i ∈ I`, and returns the next state `s' ∈ S`, where `I` is the set of possible
inputs.

![Figure 2-3: A state-transition model using a bank-account system as an example]({{ '/assets/images/diagrams/state-transition-model.svg' | relative_url }})

For a simple counter:

Pseudo notation:

```text
State space S = Integer
Input set I = {increment, decrement, reset}
Transition function:
  δ(n, increment) = n + 1
  δ(n, decrement) = n - 1
  δ(n, reset) = 0
```

### Abstracting State to Manage Complexity

Real program state spaces are enormous. Even a 64-bit memory abstraction
already suggests an enormous number of possibilities, far beyond what humans
can reason about directly.

That is why abstraction matters. We identify the parts of the state that matter
for the properties we care about and omit irrelevant detail. This produces a
manageable abstract state space.

For example, when modeling a user session in a web application:

Pseudo notation:

```text
Concrete state: every in-memory byte, TCP-connection details, and so on
Abstract state: {logged_out, logged_in, admin_session}
```

Through abstraction, billions of concrete states may be represented by only a
few meaningful abstract states.

### Invariants as Constraints on State

Not every theoretical state is valid. Systems usually have properties that must
always hold. These are invariants.

If `Valid ⊆ S` is the set of valid states, an invariant expresses the
requirement that execution should stay within `Valid`.

For a banking system:

Pseudo notation:

```text
State: a tuple of account balances (balance1, balance2, ..., balanceN)
Invariant: ∀i. balancei ≥ 0
```

### Properties of State Transitions

State transitions themselves have important properties:

- **determinism**: the same state and input always produce the same next state;
- **totality**: every state/input pair has a defined next state; and
- **partiality**: some state/input pairs do not have a defined next state and
  instead represent error cases.

Exception handling and error management are practical mechanisms for dealing
with partiality.

### State Models of Concurrent Systems

In a single-process system, state transitions are sequential. In a concurrent
system, several transitions may become possible at once, which makes the state
model far more complex.

The state of a concurrent system can often be represented as the product of the
states of its components:

Pseudo notation:

```text
S = S1 × S2 × ... × SN
```

Yet not every combination is actually reachable. Synchronization constraints
and mutual exclusion reduce the set of feasible combined states.

### Interleaving: Mathematical Description of Concurrent Execution

Concurrent execution can often be understood through interleaving: combining
the operations of each process along one time axis.

If process `P1` performs `[a, b]` and process `P2` performs `[x, y]`, possible
interleavings include:

Pseudo notation:

```text
[a, b, x, y]
[a, x, b, y]
[a, x, y, b]
[x, a, b, y]
[x, a, y, b]
[x, y, a, b]
```

This combinatorial explosion is one of the roots of concurrency complexity.
Chapter 6 studies CSP as a mathematical language for concurrency, while
Chapter 7 studies TLA+ as a way to describe more complex distributed behavior
using temporal logic.

### Exploring the State Space

Much verification in formal methods is ultimately based on exploring the state
space. Starting from an initial state, we follow all possible transitions and
inspect all reachable states.

This allows us to check properties such as:

- whether an invariant can be violated;
- whether a deadlock state can be reached;
- whether a desired target state is reachable; and
- whether a bad state is unreachable.

### Treating Time: Discrete and Continuous Models

Program systems may be modeled either in discrete time or in continuous time.

In a discrete-time model, time is represented as a sequence such as
`{0, 1, 2, ...}`, and the state at each point is defined explicitly. Many
software systems can be modeled effectively in this way.

In a continuous-time model, the state evolves over a real-valued time axis.
Such models become important in real-time systems and physical simulation.

---

## End-of-Chapter Exercises

**If you use AI while working through these exercises**
- Treat AI output as a proposal; use verifiers to determine correctness.
- Keep a record of the prompts you used, the generated specifications and
  invariants, the verification commands and logs (including seed, depth, and
  scope), and the revision history when counterexamples were found.
- See Appendix D and Appendix F for detailed templates.

### Exercise 1: Set-Theoretic Representation of a Data Structure

Represent the following data structure in set-theoretic terms:

```python
class Student:
    def __init__(self, name, age, courses):
        self.name = name        # string
        self.age = age          # integer
        self.courses = courses  # list of strings

students = [
    Student("Alice", 20, ["Math", "Physics"]),
    Student("Bob", 22, ["Chemistry", "Biology"]),
]
```

1. Express the type of the `Student` class as a Cartesian product.
2. Express the type of the `courses` field as a power set.
3. Express the type of the `students` list as a set.
4. Define a relation that determines whether a particular student is enrolled
   in a particular course.

### Exercise 2: Logic and Control Structures

Express the following natural-language conditions as logical formulas, and then
write them as program conditions:

1. "A person may drive only if they are at least 18 years old and have a valid
   license."
2. "A file may be deleted if the user is an administrator or the file owner."
3. "Every user has a valid email address."
4. "At least one product is still in stock."

### Practical Exercise: State Modeling

Model a simple vending machine as a state-transition system.

Include the following actions:
- inserting coins (100 yen and 500 yen)
- selecting a product (cola for 150 yen, tea for 100 yen)
- canceling a transaction and returning the inserted money
- calculating change

Requirements:
1. define the state space;
2. define the input set;
3. define the transition function;
4. identify at least three invariants; and
5. show a state-transition sequence for a normal purchase scenario.

### Advanced Exercise: Analysis of Concurrency

Consider the following bank-transfer system:

Pseudo notation:

```text
Account A: balance = 1000
Account B: balance = 500

Transaction 1: A → B (300 yen)
Transaction 2: B → A (200 yen)
```

If both transactions run concurrently:

1. define the state transitions for each transaction;
2. enumerate all possible interleavings;
3. calculate the result of each execution order;
4. analyze whether inconsistency can arise; and
5. propose constraints that would prevent inconsistency.

### Integrated Exercise: Preparing for Formal Methods

The following exercises are designed as a bridge into the formal methods
covered from Chapter 3 onward:

#### Exercise 1: Preparing for Alloy Modeling

Analyze the user-management subsystem of a web application from the following
perspectives:

1. **Identify entities**: define basic elements such as `User`, `Role`, and
   `Permission` as sets.
2. **Describe relations**: express mathematically relations such as "a user has
   a role" and "a role has permissions."
3. **Formalize constraints**: express business rules such as "there must be at
   least one administrator" in predicate logic.
4. **Identify invariants**: express the properties that must always hold in the
   system.

**Why this exercise matters**: it prepares the modeling mindset used in
Chapter 4.

#### Exercise 2: Preparing for Z Notation

Analyze the basic operations of a bank-account system as state transformations:

1. **State schema**: define the account state, including balance and account
   number, as a set of variables.
2. **Operation schemas**: describe deposit, withdrawal, and transfer using
   preconditions and postconditions.
3. **Error handling**: formalize exceptional situations such as insufficient
   funds.
4. **Operation composition**: describe compound operations built from multiple
   basic operations.

**Why this exercise matters**: it prepares the state-and-operation viewpoint
used in Chapter 5.

#### Exercise 3: Foundations of CSP Concurrency

Analyze client-server communication in a chat system:

1. **Identify processes**: describe the client, server, and message queue as
   concurrent processes.
2. **Communication channels**: express synchronized send/receive behavior
   mathematically.
3. **Protocol design**: specify ordering constraints for login, message
   sending, and logout.
4. **Deadlock analysis**: identify possible concurrency problems.

**Why this exercise matters**: it prepares the concurrency viewpoint used in
Chapter 6.

#### Exercise 4: Foundations of TLA+ Temporal Logic

Analyze the consistency of a distributed file system from a temporal
perspective:

1. **State variables**: define file versions and replica state as functions of
   time.
2. **Safety properties**: express timeless safety properties such as "data is
   not lost" and "consistency is preserved."
3. **Liveness properties**: express progress properties such as "a request is
   eventually processed."
4. **Temporal constraints**: express time-dependent constraints such as update
   order and timeout behavior.

**Why this exercise matters**: it prepares the temporal and distributed-systems
viewpoint used in Chapter 7.

Through these exercises, you can develop a firm foundation for the formal
specification techniques introduced from Chapter 3 onward by making the
correspondence between programming concepts and mathematical concepts explicit.
The next chapter builds on those concepts to show how to write specifications
that eliminate ambiguity.
