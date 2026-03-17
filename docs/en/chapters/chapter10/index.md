---
layout: book
title: "Chapter 10: Program Verification"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter10.md"
---
# Chapter 10: Program Verification

## 10.1 Program Correctness: The Point Where Theory Meets Practice

### The Fundamental Question of Program Verification

"Does this program behave correctly?" That simple question sits at the center
of software engineering. But what does *correctly* mean? Does it mean behaving
as expected, following a specification, or handling all intended inputs
properly?

Program verification is the discipline of turning that ambiguous notion of
correctness into a mathematically precise statement and then proving it through
logic. The formal methods introduced in the earlier chapters ultimately aim at
guaranteeing the correctness of actual program code.

Its importance is rising because software has become both more complex and more
socially consequential. Control software for autonomous vehicles, medical
devices, financial systems, and flight-control systems all operate in domains
where a programming error can lead directly to loss of life or major economic
damage.

### Where Verification Fits in the Evolution of Quality Assurance

Traditional software quality assurance has relied mainly on testing: unit
tests, integration tests, system tests, and acceptance tests. These methods
remain important and continue to contribute substantially to quality.

![Figure 10-1: The correctness-verification pyramid and the relationship between assurance and verification cost]({{ '/assets/images/diagrams/correctness-verification-pyramid-en.svg' | relative_url }})

Testing, however, has an inherent limitation. It can confirm behavior for
particular inputs, but it cannot guarantee correctness for *all* possible
inputs. As Edsger Dijkstra famously put it, testing can show the presence of
bugs, not their absence.

Program verification addresses that limit. By means of mathematical proof, it
can guarantee that a program satisfies its specification for every possible
execution considered by the model. That is a genuine shift in the quality
assurance paradigm.

### An Analogy with Structural Engineering

In civil engineering, structural calculation provides mathematical assurance of
the safety of buildings and bridges. Material strength, load distribution, and
stress concentration are analyzed according to physical law. No modern
high-rise building is constructed without such analysis.

Program verification is the software-engineering analogue of structural
calculation. It reasons mathematically about logical structure, data flow,
control flow, and program state in order to establish correctness.

This is more than a metaphor. Both disciplines provide mathematical assurance
for complex systems whose failure would be unacceptable. Just as structural
calculation is a marker of maturity in civil engineering, program verification
is a marker of maturity in software engineering.

### Two Aspects of Correctness: Partial and Total

Program correctness has two important aspects.

**Partial correctness** means: "If the program terminates, the result is
correct." Non-termination is not ruled out, but any terminating run produces a
correct outcome.

**Total correctness** means: "The program terminates, and the result is
correct." It adds termination to partial correctness.

This distinction matters in practice. Many real projects establish partial
correctness first and tackle termination separately, because proving
termination is often harder.

### Verifiability as a Design Principle

When software is developed with verification in mind, *verifiability* becomes
an important design principle. The goal is to design code in a way that makes
verification feasible.

Principles that increase verifiability include:

- **clear specifications** with little ambiguity
- **simple control flow** that is easy to reason about
- **explicit invariants** stating what must always hold
- **controlled side effects** to reduce unexpected state change

These principles do not help verification alone. In general, verifiable
programs are easier to understand, maintain, and evolve.

### The Relationship to Formal Specifications

Program verification is closely connected to the formal specification methods
introduced earlier in the book. A system may first be described in Z, Alloy,
or TLA+, and then implemented in a programming language. Verification then
proves that the implementation satisfies the specification.

This relationship is not one-way. During verification, incompleteness or
ambiguity in the specification is often discovered. Verification therefore
improves both the code and the specification.

### From the Alloy Models of Chapter 4 to Program Verification

The Alloy modeling you learned in Chapter 4 is a useful preparation for
program verification. Properties described in Alloy can be carried into an
implementation-level proof using Hoare logic.

```alloy
// Banking-account system in Alloy (Chapter 4)
sig Account { balance: Int }
pred transfer[from, to: Account, amount: Int] {
    from.balance >= amount
    from.balance' = from.balance - amount
    to.balance' = to.balance + amount
}
assert NoNegativeBalance {
    all a: Account | a.balance >= 0
}
```

At implementation level, the same intent may be expressed as a Hoare-style
contract:

```text
{from.balance >= amount ∧ to.balance >= 0}
  transfer(from, to, amount)
{from.balance >= 0 ∧ to.balance >= 0}
```

### Managing Levels of Abstraction

Choosing the right abstraction level is essential in practical verification. If
the model is too low-level, the proof becomes intractable. If it is too
high-level, critical details are lost.

A layered approach is often effective:

- **algorithm level**: correctness of data structures and core operations
- **module level**: interaction among functions or procedures
- **system level**: overall architecture and integrated behavior

Higher layers can then rely on established results from lower layers.

### Balancing Cost and Practicality

Program verification is powerful, but full verification of everything is rarely
economically realistic. Practical teams therefore vary the verification effort
according to criticality:

- **safety-critical parts**: full verification
- **important functions**: verification of main properties
- **general functionality**: conventional testing and lighter analysis

This staged approach makes it possible to achieve the highest return from
limited resources.

### Tool Progress and Practical Deployment

Program-verification tools have improved significantly in recent years.
Automatic theorem proving, SMT solving, and verification-condition generation
have all advanced enough that practical verification is no longer purely
theoretical.

Large technology companies such as Microsoft, Amazon, and Meta have begun to
apply formal verification techniques to production systems. That change signals
that program verification is moving from research practice into engineering
practice.

Program verification is therefore a bridge between theory and real software
development. The next section introduces Hoare logic, the classical logical
foundation for this area.

## 10.2 Hoare Logic: A Logic of Programs

### The Innovation of Expressing Program Behavior in Logic

Hoare logic, proposed in 1969 by C.A.R. Hoare, is a logical system for
reasoning about program correctness. Its innovation was to express program
behavior in a mathematically precise form amenable to proof.

The core idea is to treat each program fragment as a kind of *contract*: if a
precondition holds before execution, then a postcondition is guaranteed after
execution. That perspective makes logical reasoning about programs possible.

### Hoare Triples: The Basic Unit of Program Reasoning

The basic form of Hoare logic is the *Hoare triple*:

```text
{P} S {Q}
```

Here:

- **`P`** is the precondition
- **`S`** is the program statement
- **`Q`** is the postcondition

The meaning is: if the initial state satisfies `P`, then after executing `S`,
the final state satisfies `Q`. This describes partial correctness; termination
is not yet guaranteed.

### Understanding Through Concrete Examples

A very simple assignment example:

```text
{x = 5} x := x + 1 {x = 6}
```

This states that if `x` starts as 5, then after `x := x + 1`, it becomes 6.

A more general version:

```text
{x = n} x := x + 1 {x = n + 1}
```

A conditional example:

```text
{x >= 0}
if x > 0 then y := 1 else y := 0
{(x > 0 ∧ y = 1) ∨ (x = 0 ∧ y = 0)}
```

The postcondition reflects both execution paths.

### Weakest Preconditions and Strongest Postconditions

Two important concepts underpin Hoare logic:

- **weakest precondition** `WP(S, Q)`: the weakest condition sufficient to
  guarantee postcondition `Q` after running `S`
- **strongest postcondition** `SP(P, S)`: the strongest property guaranteed
  after running `S` from a state satisfying `P`

Example:

```text
WP(x := x + 1, x > 10) = x > 9
```

To end with `x > 10`, the input state must satisfy `x > 9`.

Another example:

```text
SP(x > 5, x := x * 2) = x > 10 ∧ x is even
```

These notions are fundamental for verification-condition generation and proof
automation.

### The Rule for Assignment

Assignment is the simplest program construct, and its rule forms the basis of
Hoare logic.

**Assignment axiom**:

```text
{Q[E/x]} x := E {Q}
```

Here, `Q[E/x]` means "substitute expression `E` for every free occurrence of
`x` in `Q`."

This feels backwards at first: the proof computes the precondition from the
desired postcondition. But that is exactly what makes the effect of assignment
precise.

Example:

```text
{x + 1 > 10} x := x + 1 {x > 10}
```

Since `x + 1 > 10` is equivalent to `x > 9`, the rule captures the intended
meaning exactly.

### Sequential Composition

To reason about multiple statements executed in order, Hoare logic uses the
composition rule:

```text
{P} S1 {R}, {R} S2 {Q}
─────────────────────────
{P} S1; S2 {Q}
```

If the postcondition of `S1` is strong enough to serve as the precondition of
`S2`, then the entire sequence is correct.

Example:

```text
{x = 5} x := x + 1 {x = 6}
{x = 6} y := x * 2 {y = 12 ∧ x = 6}
─────────────────────────────────────
{x = 5} x := x + 1; y := x * 2 {y = 12 ∧ x = 6}
```

### Conditionals

For conditionals, both branches must be considered:

```text
{P ∧ B} S1 {Q}, {P ∧ ¬B} S2 {Q}
──────────────────────────────────
{P} if B then S1 else S2 {Q}
```

Example:

```text
{x ≠ 0 ∧ x > 0} y := x {y > 0}
{x ≠ 0 ∧ ¬(x > 0)} y := -x {y > 0}
────────────────────────────────────
{x ≠ 0} if x > 0 then y := x else y := -x {y > 0}
```

Each branch separately establishes the same overall postcondition.

### Weakening and Strengthening

Real proofs often require adapting conditions:

**Strengthening the precondition**:

```text
P' ⇒ P, {P} S {Q}
──────────────────
{P'} S {Q}
```

**Weakening the postcondition**:

```text
{P} S {Q}, Q ⇒ Q'
──────────────────
{P} S {Q'}
```

These rules provide the flexibility needed in practical proofs.

### The Concept of an Invariant

An *invariant* is a property that remains true throughout execution.

Example of a data invariant:

```text
∀i,j. 0 ≤ i < j < length(array) ⇒ array[i] ≤ array[j]
```

This states that the array is always sorted.

Example of a loop invariant:

```text
sum = Σ(k=0 to i-1) array[k]
```

This states that `sum` equals the total of all elements processed so far.

Invariants are one of the most important tools for structuring correctness
proofs.

### Relationship to Contract-Based Programming

The core idea of Hoare logic strongly influenced *design by contract*. In that
style, functions or methods explicitly declare preconditions, postconditions,
and invariants.

Example in Java with JML:

```java
/*@ requires x >= 0;
  @ ensures \result >= 0 && \result * \result <= x &&
  @         (\result + 1) * (\result + 1) > x;
  */
public int sqrt(int x) {
    // square-root implementation
}
```

This makes the intended behavior explicit and enables both runtime and static
checking.

### Soundness and Completeness

Hoare logic has two classical theoretical properties:

- **soundness**: any triple provable in the logic is semantically correct
- **completeness**: any semantically correct triple is, in principle, provable
  in the logic

For practice, soundness is indispensable. If the logic can prove false claims,
verification loses its value.

### Modern Extensions

Basic Hoare logic has been extended in many ways to fit modern programming
languages:

- **separation logic** for pointers and heap reasoning
- **concurrent Hoare logic** for concurrent programs
- **probabilistic Hoare logic** for probabilistic programs
- **quantum Hoare logic** for quantum software

These extensions allow the core insight of Hoare logic to remain relevant in
modern verification.

Hoare logic provides a durable theoretical foundation for program verification.
The next section applies this logic to concrete programming constructs.

## 10.3 Verification Rules for Basic Syntax

### Systematic Verification of Program Syntax

Programs are composed of basic syntactic building blocks: assignment,
conditionals, loops, procedure calls, and so on. Verification rules are
defined for each such construct. By composing these rules, we can verify more
complex programs step by step.

Understanding these rules is essential, because every large program ultimately
reduces to combinations of these basic forms.

### A Detailed Look at Assignment

Assignment is simple in syntax but conceptually deep in verification.

**Basic assignment rule**:

```text
{Q[E/x]} x := E {Q}
```

The reason this runs "backward" is that proof typically starts from the desired
postcondition and computes what must already have been true beforehand.

Simple examples:

```text
{5 > 3} x := 5 {x > 3}
```

```text
{y + 1 > 3} x := y + 1 {x > 3}
```

```text
{2 * (y + 1) > 10} x := 2 * (y + 1) {x > 10}
```

The last one simplifies to:

```text
{y > 4} x := 2 * (y + 1) {x > 10}
```

For multiple assignments, care is needed.

Simultaneous assignment:

```text
{x + y = z + w} x, y := z, w {x + y = z + w}
```

Sequential assignment:

```text
{E2[E1/x] = F} x := E1; y := E2 {y = F}
```

The key subtlety is that occurrences of `x` inside `E2` are affected by the
earlier assignment.

### Strategies for Verifying Conditionals

Conditionals introduce branching, so verification must cover every possible
path.

**Conditional rule**:

```text
{P ∧ B} S1 {Q}, {P ∧ ¬B} S2 {Q}
──────────────────────────────────
{P} if B then S1 else S2 {Q}
```

Practical example: absolute value

```text
{true}
if x >= 0 then
    result := x
else
    result := -x
{result >= 0 ∧ (result = x ∨ result = -x)}
```

Then-branch reasoning:

```text
{x >= 0} result := x {x >= 0 ∧ (x = x ∨ x = -x)}
```

Else-branch reasoning:

```text
{x < 0} result := -x {-x >= 0 ∧ (-x = x ∨ -x = -x)}
```

In each case, the branch-specific condition is enough to establish the common
postcondition.

### Nested Conditionals

Nested branching makes path conditions more complex:

```text
{P}
if B1 then
    if B2 then S1 else S2
else
    if B3 then S3 else S4
{Q}
```

The path-specific premises are:

- path 1: `P ∧ B1 ∧ B2`
- path 2: `P ∧ B1 ∧ ¬B2`
- path 3: `P ∧ ¬B1 ∧ B3`
- path 4: `P ∧ ¬B1 ∧ ¬B3`

Good proofs make those path conditions explicit instead of reasoning about them
implicitly.

### Practical Use of Sequential Composition

Sequential composition is the main way to decompose a complex program into
manageable fragments.

Example: swapping two variables

```text
{x = a ∧ y = b}
temp := x;
x := y;
y := temp
{x = b ∧ y = a}
```

A stepwise analysis yields:

1. `{x = a ∧ y = b} temp := x {temp = a ∧ x = a ∧ y = b}`
2. `{temp = a ∧ x = a ∧ y = b} x := y {temp = a ∧ x = b ∧ y = b}`
3. `{temp = a ∧ x = b ∧ y = b} y := temp {temp = a ∧ x = b ∧ y = a}`

From the final state, the desired postcondition follows immediately.

### Block Structure and Scope

Modern programming languages use blocks to delimit variable scope.

```text
{P} var x := E; S {Q}
```

In this setting, `x` must not appear free in `Q`, because `x` is local to the
block.

Example:

```text
{y > 0}
var temp := y * 2;
result := temp + 1
{result > 1}
```

### Error Handling and Exceptions

Real programs also contain exceptional behavior:

```text
{P}
if valid_input(x) then
    result := process(x)
else
    error("Invalid input")
{valid_input(x) ⇒ result = process(x)}
```

The postcondition guarantees the normal case only when the input is valid; the
invalid path is handled through explicit error behavior.

### Functions and Procedures

Verification of function calls relies on their contracts.

```text
{P[E/x]} y := f(E) {Q[y/result]}
```

If a function `f` has a contract `{P'} f(x) {Q'}`, then the call site must
establish `P[E/x] ⇒ P'`, and the function's postcondition must imply the
desired caller-side postcondition.

Example:

```text
(* Specification of sqrt:
   {x >= 0} sqrt(x) {result * result <= x < (result+1)*(result+1)} *)

{16 >= 0} y := sqrt(16) {y * y <= 16 < (y+1)*(y+1)}
```

### Practical Verification Strategy

Useful proof strategies for basic syntax include:

1. **backward reasoning** from the postcondition
2. **forward reasoning** from the precondition
3. **strategic choice of intermediate assertions** in sequential composition
4. **explicit use of invariants** for properties that remain stable

Once these basic rules are well understood, larger program proofs become much
more systematic.

## 10.4 Loop Invariants: The Essence of Repetition

### Why Loops Are Fundamentally Difficult

Loops are among the hardest program constructs to verify because they may
iterate an arbitrary number of times. A finite proof must account for an
unbounded set of possible executions.

Consider:

```text
i := 0;
while i < n do
    i := i + 1
```

Depending on `n`, the loop may run 0 times, 100 times, 1000 times, or more.
Yet verification must cover all those possibilities at once.

The key concept that makes this possible is the *loop invariant*.

### Invariance Amid Change

A loop invariant is a property that remains true throughout loop execution. The
idea is closely related to mathematical induction.

In ordinary induction:

1. base case: prove `P` for 0
2. inductive step: prove `P(k) -> P(k+1)`
3. conclude `P(n)` for all `n`

For loops:

1. initialization: the invariant holds before the loop starts
2. preservation: one loop iteration preserves the invariant
3. termination: invariant plus loop exit condition imply the target
   postcondition

### The Formal While Rule

The classical rule for `while` loops is:

```text
{I ∧ B} S {I}, I ∧ ¬B ⇒ Q
────────────────────────────────
{I} while B do S {Q}
```

Here:

- `I` is the loop invariant
- `B` is the loop condition
- `S` is the loop body
- `Q` is the desired postcondition

### Understanding Through Examples

**Example 1: a simple counting loop**

```text
{n >= 0}
i := 0;
while i < n do
    i := i + 1
{i = n}
```

Loop invariant:

```text
I: 0 <= i <= n
```

Verification outline:

1. **Initialization**: after `i := 0`, `0 <= i <= n` holds if `n >= 0`
2. **Preservation**: under `0 <= i <= n ∧ i < n`, executing `i := i + 1`
   preserves `0 <= i <= n`
3. **Exit**: from `0 <= i <= n ∧ i >= n`, we derive `i = n`

**Example 2: summing array elements**

```text
{n >= 0 ∧ n = length(a)}
sum := 0;
i := 0;
while i < n do
    sum := sum + a[i];
    i := i + 1
{sum = Σ(k=0 to n-1) a[k]}
```

Loop invariant:

```text
I: 0 <= i <= n ∧ sum = Σ(k=0 to i-1) a[k]
```

This states that the loop has correctly accumulated the prefix processed so
far.

### Techniques for Discovering Invariants

Finding the right invariant is usually the most creative part of loop
verification.

**Technique 1: generalize the goal**

If the final goal is:

```text
result = n!
```

then a useful invariant is often a generalization such as:

```text
result = i! ∧ 0 <= i <= n
```

**Technique 2: inspect concrete executions**

```text
Initial: i=0, sum=0
Step 1:  i=1, sum=a[0]
Step 2:  i=2, sum=a[0]+a[1]
Step 3:  i=3, sum=a[0]+a[1]+a[2]
```

The pattern suggests:

```text
sum = Σ(k=0 to i-1) a[k]
```

**Technique 3: derive invariants from data-structure properties**

For search in a binary-search tree:

```text
left <= target <= right ∧
(target ∈ tree ⇒ left <= target <= right)
```

### Analyzing More Complex Loops

**Nested loops**

```text
{n >= 0 ∧ m >= 0}
i := 0;
while i < n do
    j := 0;
    while j < m do
        matrix[i][j] := 0;
        j := j + 1;
    i := i + 1
{∀i,j. 0 <= i < n ∧ 0 <= j < m ⇒ matrix[i][j] = 0}
```

Outer-loop invariant:

```text
0 <= i <= n ∧
∀i',j'. 0 <= i' < i ∧ 0 <= j' < m ⇒ matrix[i'][j'] = 0
```

Inner-loop invariant:

```text
0 <= j <= m ∧
∀j'. 0 <= j' < j ⇒ matrix[i][j'] = 0
```

**Condition-dependent loops**

```text
while (condition1 ∧ condition2) do
    if B then
        S1
    else
        S2
```

The invariant must be preserved by both paths through the loop body.

### Proving Termination

To obtain total correctness, termination must also be proved. This is done
with a *variant function*.

A variant `V` should satisfy:

1. **non-negativity**: `V >= 0`
2. **strict decrease**: each loop iteration decreases `V`

Example: counting loop

```text
V = n - i
```

Each iteration increases `i`, so `V` decreases by 1 until it reaches 0.

Example: binary search

```text
V = right - left
```

The search range shrinks on every iteration, so the variant decreases.

### Practical Loop Patterns

**Pattern 1: linear search**

```text
Invariant:
  0 <= i <= n ∧
  ∀k. 0 <= k < i ⇒ a[k] ≠ target
Variant:
  n - i
```

**Pattern 2: insertion sort**

```text
Invariant:
  0 <= i <= n ∧
  sorted(a[0..i-1]) ∧
  ∀k,j. 0 <= k < i ∧ i <= j < n ⇒ a[k] <= a[j]
Variant:
  n - i
```

**Pattern 3: binary search**

```text
Invariant:
  0 <= left <= right <= n ∧
  (target ∈ a ⇒ left <= target_index < right)
Variant:
  right - left
```

### Strengthening and Weakening Invariants

In practice, invariants often require adjustment.

- **strengthening**: add information that makes the proof easier
- **weakening**: remove information that cannot actually be preserved

Example: finding the maximum element in an array

Initial attempt:

```text
max = maximum(a[0..i-1])
```

Problem: this is undefined when `i = 0`.

Refined invariant:

```text
i > 0 ⇒ max = maximum(a[0..i-1])
```

### Debugging Loop Proofs

When an invariant proof fails, practical recovery steps include:

1. manually executing the loop on a small example
2. refining boundary conditions and special cases
3. splitting one complex invariant into several simpler ones

Loop invariants are one of the most powerful concepts in program verification.
They capture the stable structure hidden inside repetition and make rigorous
reasoning about loops possible.

## 10.5 Arrays and Pointers: Verifying Memory Operations

### Why Memory Verification Is Complex

Arrays and pointers are indispensable in practical software, but verifying them
is far harder than verifying basic syntax. The difficulty comes from several
sources:

- **aliasing**: multiple pointers may refer to the same memory region
- **shared mutable state**: more than one name may update the same storage
- **uncertain bounds**: valid array ranges can depend on runtime values
- **ownership complexity**: it may be unclear which code is allowed to mutate
  which memory region

Classical Hoare logic alone does not handle these issues well. That is why
*separation logic* was introduced.

### Basic Verification of Array Access

Start with the simplest case.

**Reading from an array**:

```text
{0 <= i < length(a)} x := a[i] {x = a[i]}
```

Even here, a precise bounds check is part of the required precondition.

**Writing to an array**:

```text
{0 <= i < length(a)} a[i] := x {a[i] = x ∧ ...}
```

The hard part is the omitted `...`: we also need to describe what happens to
every element *other than* `a[i]`.

```text
{0 <= i < length(a)}
a[i] := x
{a[i] = x ∧ ∀j. j ≠ i ⇒ a[j] = old(a[j])}
```

Here `old(a[j])` denotes the value of `a[j]` before the assignment.

### The Frame Problem and Separation Logic

The *frame problem* is the burden of describing everything that did *not*
change. In the array-update example, that means explicitly describing all
unchanged elements.

Separation logic addresses this through the idea of *separation*: memory is
treated as a collection of disjoint heap regions.

Core notions:

- **empty heap**: `emp`
- **points-to assertion**: `x ↦ v`
- **separating conjunction**: `P * Q`

Example:

```text
x ↦ 5 * y ↦ 3
```

This means that `x` points to 5 and `y` points to 3 in disjoint memory
regions.

### Describing Arrays in Separation Logic

An array can be represented as a contiguous memory segment.

**Array segment**:

```text
array[i..j) ↦ [v₁, v₂, ..., vₙ]
```

This states that `array[i]` through `array[j-1]` occupy consecutive memory and
contain the listed values.

**Array read in separation logic**:

```text
{array[0..n) ↦ [v₀, v₁, ..., vₙ₋₁] ∧ 0 <= i < n}
x := array[i]
{x = vᵢ ∧ array[0..n) ↦ [v₀, v₁, ..., vₙ₋₁]}
```

**Array write in separation logic**:

```text
{array[0..n) ↦ [v₀, v₁, ..., vₙ₋₁] ∧ 0 <= i < n}
array[i] := w
{array[0..n) ↦ [v₀, ..., vᵢ₋₁, w, vᵢ₊₁, ..., vₙ₋₁]}
```

### Verifying Pointer Operations

Pointers introduce still more complexity. Avoiding null dereference and memory
leak is essential.

**Pointer read**:

```text
{p ↦ v ∧ p ≠ null} x := *p {x = v ∧ p ↦ v}
```

**Pointer write**:

```text
{p ↦ _ ∧ p ≠ null} *p := x {p ↦ x}
```

**Allocation**:

```text
{emp} p := malloc() {p ↦ _ ∧ p ≠ null}
```

**Deallocation**:

```text
{p ↦ _ ∧ p ≠ null} free(p) {emp}
```

### Verifying Linked Structures

Recursive data structures such as linked lists and trees are usually specified
with *inductive predicates*.

Linked list example:

```text
list(head, elements) ≡
  (head = null ∧ elements = []) ∨
  ∃x, next, tail. head ↦ {data: x, next: next} *
                   list(next, tail) ∧
                   elements = x::tail
```

This states that a list is either empty or consists of a node followed by a
smaller list.

Insertion at the head:

```text
{list(head, elements)}
newNode := malloc();
newNode.data := x;
newNode.next := head;
head := newNode
{list(head, x::elements)}
```

### Verifying an Array Sorting Algorithm

As a practical example, consider insertion sort:

```text
{array[0..n) ↦ input ∧ n >= 0}
for i := 1 to n-1 do
    key := array[i];
    j := i - 1;
    while j >= 0 ∧ array[j] > key do
        array[j+1] := array[j];
        j := j - 1;
    array[j+1] := key
{array[0..n) ↦ output ∧ sorted(output) ∧ permutation(input, output)}
```

Outer-loop invariant:

```text
1 <= i <= n ∧
array[0..i) ↦ partial_sorted ∧
array[i..n) ↦ remaining ∧
sorted(partial_sorted) ∧
permutation(input, partial_sorted ++ remaining)
```

Inner-loop invariant:

```text
-1 <= j < i ∧
array[0..j+1) ↦ left_part ∧
array[j+1..i+1) ↦ shifted_part ∧
array[i+1..n) ↦ unchanged ∧
sorted(left_part) ∧
∀x ∈ left_part. x <= key ∧
∀x ∈ shifted_part. x > key
```

### An Example of Aliasing

Aliasing is a major source of proof complexity:

```text
{array[0..n) ↦ values}
p := &array[i];
q := &array[j];
*p := x;
*q := y;
{(i = j ⇒ array[i] ↦ y) ∧ (i ≠ j ⇒ array[i] ↦ x * array[j] ↦ y)}
```

If `i = j`, both pointers refer to the same cell and the final value is `y`. If
`i ≠ j`, the two writes affect disjoint cells.

Separation logic expresses this as:

```text
{(i = j ⇒ array[i] ↦ _) ∧ (i ≠ j ⇒ array[i] ↦ _ * array[j] ↦ _)}
...
{(i = j ⇒ array[i] ↦ y) ∧ (i ≠ j ⇒ array[i] ↦ x * array[j] ↦ y)}
```

### Ownership and Borrowing

Modern languages such as Rust address memory safety through *ownership*.

Typical ownership rules are:

1. each memory region has a unique owner
2. when the owner leaves scope, memory is released automatically
3. at any point, there is either one mutable reference or multiple immutable
   references

These rules push many memory-safety guarantees into the type system itself.

### Integration with Verification Tools

Practical memory verification often relies on dedicated tools.

**Array verification in Dafny**:

```dafny
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
  modifies nothing
```

**Array verification in SPARK**:

```ada
procedure Binary_Search (A : Integer_Array; Key : Integer;
                         Found : out Boolean; Index : out Natural)
  with Pre  => A'Length > 0 and then
                 (for all I in A'Range =>
                    (for all J in I+1 .. A'Last => A(I) <= A(J))),
       Post => (if Found then A(Index) = Key else
                  (for all I in A'Range => A(I) /= Key));
```

### Practical Strategy for Memory Verification

Useful practical guidelines include:

1. **make ownership explicit**
2. **treat boundary conditions rigorously**
3. **analyze possible aliasing patterns up front**
4. **decompose complex memory operations**
5. **use automation where manual proof is too expensive**

Memory verification is one of the most challenging parts of practical program
verification, but it is also one of the most valuable in real systems.

## 10.6 Practical Program Verification: Tools and Methodology

### Bridging Theory and Practice

How are the theoretical foundations of this chapter used in real projects?
Moving from classroom examples to production systems requires tools and
methodology that close the gap between theory and engineering reality.

The goal of practical program verification is not theoretical perfection for
its own sake. It is *economically rational improvement in trustworthiness*.
Teams must use limited time and budget to verify the properties that matter
most.

### Categories of Verification Tools

Modern tools can be divided into several broad categories.

**Static-analysis tools** inspect code without executing it:

- **type checkers** for type safety
- **linters** for coding-policy and basic defect checks
- **abstract-interpretation tools** for runtime-error detection

**Contract-based verification tools** work from explicit specifications:

- **Dafny**
- **SPARK**
- **ACSL/Frama-C**

**Proof assistants** provide the strongest level of assurance, but also the
highest learning and deployment cost:

- **Rocq**
- **Isabelle/HOL**
- **Lean**

### From Hoare Logic to Mechanization

Hoare logic and loop invariants can be used on paper, but once mechanized,
claims, assumptions, and proofs become version-controlled assets.

In proof assistants such as Lean, Rocq, or Isabelle, the Hoare triple itself
can be encoded as a proposition whose proof is checked by the kernel.

Here is a deliberately simplified Lean-style formulation:

```lean
def Hoare {S : Type} (P : S -> Prop) (C : S -> S) (Q : S -> Prop) : Prop :=
  forall s : S, P s -> Q (C s)
```

This perspective supports several practical design decisions:

- automate the regions that lightweight tools such as Dafny can handle
- reserve proof-assistant effort for the core logical arguments
- delay mechanization of unstable interfaces until the abstraction boundary is
  clear

### Dafny: Practical Verification-Oriented Programming

Dafny allows specifications and implementations to live in the same language.
It was created at Microsoft Research and is used both pedagogically and
practically.

```dafny
method Max(a: int, b: int) returns (max: int)
  ensures max >= a && max >= b
  ensures max == a || max == b
{
  if a >= b {
    max := a;
  } else {
    max := b;
  }
}
```

The `ensures` clauses express the postcondition. Dafny verifies automatically
that the implementation satisfies it.

Loop invariants are likewise written explicitly:

```dafny
method Sum(arr: array<int>) returns (sum: int)
  requires arr.Length > 0
  ensures sum == arr[0] + arr[1] + ... + arr[arr.Length-1]
{
  sum := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant sum == arr[0] + arr[1] + ... + arr[i-1]
  {
    sum := sum + arr[i];
    i := i + 1;
  }
}
```

### SPARK: Proven Industrial Use

SPARK is a contract-based verification technology used in safety-critical
domains such as aerospace, rail, and automotive systems.

Characteristics of SPARK include:

- a disciplined subset of Ada
- staged application from partial specifications to stronger guarantees
- integration into industrial toolchains

```ada
procedure Increment (X : in out Integer)
  with Pre  => X < Integer'Last,
       Post => X = X'Old + 1;

procedure Increment (X : in out Integer) is
begin
   X := X + 1;
end Increment;
```

### The Reach and Limits of Automation

Modern tools automate many proof obligations, but not all of them.

**Areas that automate well**:

- type safety
- linear arithmetic and bounds checks
- simple list and array manipulations
- recurring proof patterns

**Areas that still need human guidance**:

- discovering nontrivial invariants
- choosing proof strategies
- refining an informal requirement into a formal specification
- balancing proof strength against engineering cost

Knowing where automation stops is part of mature verification practice.

### SMT Solvers

SMT (Satisfiability Modulo Theories) solvers are a core technology behind many
modern verification tools. They decide satisfiability of logical formulas over
theories such as arithmetic, arrays, and bit-vectors.

They are especially effective for:

- linear arithmetic
- array reads and writes
- bit-vector reasoning
- quantifier-free first-order reasoning

Major SMT solvers include:

- **Z3**
- **CVC4/CVC5**
- **Yices**

### A Practical Verification Workflow

A realistic project workflow often looks like this:

**1. Requirements analysis and property extraction**

- identify which properties actually need verification
- prioritize safety, security, and functional correctness

**2. Incremental formalization**

- start from the most critical properties
- express them in a machine-checkable form
- validate that the formalization matches the intent

**3. Incremental verification of the implementation**

- unit-level verification
- module-level composition
- system-level verification

**4. Analysis and refinement**

- investigate why a proof failed
- repair the code or the specification
- decide on fallback techniques where full proof is too expensive

### Cost-Benefit Analysis

Practical program verification requires explicit assessment of cost and value.

**Costs**:

- learning cost for the team
- tool licensing and maintenance
- extra development time for specifications and proofs
- maintenance cost to keep code and specs aligned

**Benefits**:

- earlier defect detection
- reduced testing cost for verified parts
- stronger assurance
- improved maintainability through clearer specifications

### A Staged Adoption Strategy

Organizations usually adopt verification in stages.

**Phase 1: lightweight tools**

- static analysis
- automatic policy checks
- better use of the type system

**Phase 2: contract-based programming**

- preconditions and postconditions on important functions
- unit-level proof practice
- accumulation of specification-writing skill

**Phase 3: system-level verification**

- contracts between modules
- full verification of critical algorithms
- stricter assurance for safety-critical parts

### Success Factors in Real Projects

Successful verification in real projects depends on three kinds of factors.

**Technical factors**:

- choosing suitable tools
- managing complexity incrementally
- adopting verification-friendly designs

**Organizational factors**:

- management support
- team-wide skill development
- willingness to invest with a long-term perspective

**Process factors**:

- integration with the existing development workflow
- continuous improvement
- accumulation and sharing of knowledge

Practical program verification succeeds when theory, tooling, and organizational
discipline reinforce one another.

---

## End-of-Chapter Exercises

Treat these as verification design drills. A worked proof sketch, verifier log,
or short technical note is enough as long as the correctness argument is
explicit.

### Basic Exercise 1: Foundations of Hoare Logic

Construct suitable Hoare triples for the following program fragments.

**Exercise 1-1: basic assignments**

```text
x := y + 2;
z := x * 3;
```

Target postcondition:

```text
z = 3 * (y + 2)
```

**Exercise 1-2: conditional**

```text
if x > 0 then
    result := x
else
    result := -x
```

Target postcondition:

```text
result ≥ 0
```

**Exercise 1-3: simple loop**

```text
sum := 0;
i := 1;
while i <= n do
    sum := sum + i;
    i := i + 1
```

Target postcondition:

```text
sum = n * (n + 1) / 2
```

For each exercise:

1. choose an appropriate precondition
2. identify intermediate assertions if needed
3. state a loop invariant when a loop is present
4. explain each proof step logically

### Basic Exercise 2: Finding Loop Invariants

For each of the following algorithms, discover a suitable loop invariant and
prove correctness.

**Exercise 2-1: linear search**

```text
found := false;
i := 0;
while i < n && !found do
    if array[i] = target then
        found := true;
        position := i;
    i := i + 1;
```

**Exercise 2-2: maximum search**

```text
max := array[0];
i := 1;
while i < n do
    if array[i] > max then
        max := array[i];
    i := i + 1;
```

**Exercise 2-3: insertion sort**

```text
for i := 1 to n-1 do
    key := array[i];
    j := i - 1;
    while j >= 0 && array[j] > key do
        array[j+1] := array[j];
        j := j - 1;
    array[j+1] := key;
```

For each algorithm:

1. propose a suitable loop invariant
2. prove initialization, preservation, and termination reasoning
3. identify a variant function that ensures termination

### Practical Exercise 1: Verifying Array Algorithms

Choose one of the following algorithms and prove its full correctness.

**Option 1: binary search**

```text
left := 0;
right := n - 1;
found := false;
while left <= right && !found do
    mid := (left + right) / 2;
    if array[mid] = target then
        found := true;
        position := mid;
    else if array[mid] < target then
        left := mid + 1;
    else
        right := mid - 1;
```

**Option 2: bubble sort**

```text
for i := 0 to n-2 do
    for j := 0 to n-2-i do
        if array[j] > array[j+1] then
            temp := array[j];
            array[j] := array[j+1];
            array[j+1] := temp;
```

**Option 3: quicksort (simplified)**

```text
procedure quicksort(array, low, high):
    if low < high then
        pivot := partition(array, low, high);
        quicksort(array, low, pivot - 1);
        quicksort(array, pivot + 1, high);
```

Verification items:

1. clarify the precondition and postcondition
2. identify all required loop invariants
3. guarantee array-bound safety
4. prove functional correctness
5. prove termination

### Practical Exercise 2: Tool-Assisted Verification

Use an actual verification tool such as Dafny or SPARK to implement and verify
the following specification:

```text
Function specification:
  Input: integer array array[0..n-1] (n > 0)
  Output: a Boolean telling whether the array is a palindrome

  Precondition: array != null && array.length > 0
  Postcondition:
    result == true ⇔ ∀i. 0 ≤ i < n ⇒ array[i] == array[n-1-i]
```

Implementation requirements:

1. write appropriate preconditions and postconditions
2. state loop invariants explicitly
3. guarantee array-bound safety
4. make the tool verification succeed automatically

Suggested output:

- the full implementation
- the verification-tool output
- a short note explaining the proof obligations, tool findings, and how you
  resolved the main verification issues

### Advanced Exercise: Partial Verification of a Practical System

Choose part of a practical system and apply formal verification.

**Option 1: a simple cryptographic system**

- prove reversibility of encryption and decryption for a Caesar cipher or XOR
  cipher
- validate input strings
- guarantee memory safety

**Option 2: a fundamental data structure**

- preserve invariants of a stack, queue, or balanced tree
- prove functional correctness of operations
- prevent memory leaks

**Option 3: part of a concurrent program**

- avoid data races in a simple producer-consumer setup
- prevent deadlock
- preserve production-consumption consistency

Suggested analysis outline:

1. justify the chosen target system
2. identify the properties to verify
3. describe the formal specification
4. explain the verification approach
5. report problems found and proposed improvements
6. discuss obstacles to wider practical deployment

### Self-Review Checklist

Use the following checklist to evaluate your result.

**Accuracy**

- correctness of the mathematical reasoning
- suitability of the specification
- completeness of the proof

**Understanding**

- correct understanding and use of the concepts
- clear grasp of the essential problem structure
- appropriate choice of method

**Practicality**

- consideration of realistic constraints
- effective use of tools
- applicability to real projects

**Judgment**

- originality of the approach
- quality of handling complex problems
- quality of improvement proposals

Through these exercises, the goal is to acquire both the theoretical
foundations and the practical techniques of program verification so that you
can apply them to quality improvement in real software development.
