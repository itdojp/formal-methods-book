---
layout: book
title: "Chapter 3: Foundations of Specification"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter03.md"
---
# Chapter 3: Foundations of Specification

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter03.md`

## 3.1 What a Specification Is: A Bridge Between Ideals and Reality

### The Essential Role of Specifications

When people hear the word *specification*, many imagine a technical document or
requirements definition. In reality, the idea is broader and deeper.
Specifications are the bridge between the behavior an ideal system ought to
have and the behavior a real implementation actually exhibits.

An analogy from everyday life helps. When an architect draws a blueprint, the
drawing expresses how a building should be. It describes materials,
dimensions, layout, and structural relationships. That information allows a
builder to construct a concrete building. In the same way, a software
specification expresses how a system should behave, and developers use it as
the basis for writing concrete code.

There is, however, one important difference between architectural drawings and
software specifications. Architectural drawings mainly describe static
structure. Software specifications must also describe dynamic behavior. What
happens when a user presses a button? What happens if the database connection
fails? What happens if two users access the same resource at the same time?
These dynamic aspects are a major source of the complexity of software
specification.

### The Layered Structure of Specifications

In real software projects, specifications are structured hierarchically. They
range from top-level business requirements down to system specifications,
module specifications, and finally specifications for individual functions.

- **Business-requirement level**: "A customer can purchase a product."
- **System-specification level**: "A purchase completes through user
  authentication, inventory confirmation, payment processing, and shipping
  arrangement."
- **Module-specification level**: "The payment module validates credit
  information and executes billing."
- **Function-specification level**: "The `validateCreditCard` function accepts
  a 16-digit numeric string and checks its checksum."

This layering is not accidental. Human cognitive capacity is limited, and it is
impossible to grasp all details at once. Appropriate abstraction is therefore
necessary in order to decompose a system into levels of manageable complexity.

### The Many Facets of Specifications

A specification has several aspects.

- **Functional aspects**: what the system does
- **Non-functional aspects**: how the system behaves, including performance,
  availability, and security
- **Constraints**: what the system must not do
- **Quality attributes**: desirable properties of the system

Traditional software engineering often focused mainly on functional behavior.
In modern systems, however, non-functional properties are frequently decisive.
In cloud services such as Amazon's, requirements such as "99.99% availability"
or "response time under 100 milliseconds" may be at least as important as
functional behavior.

Formal methods provide a unified framework for describing all of these aspects.

### The Evolutionary Nature of Specifications

A software specification is not static. It evolves continuously in response to
changing requirements, technological progress, and what users learn through
actual use.

One advantage of formal specifications is that they make the impact of change
clearer. When one element of a specification changes, it becomes possible to
analyze mathematically which other parts are affected. That, in turn, helps a
team distinguish safe changes from dangerous ones and apply verification where
it matters.

## 3.2 Fighting Ambiguity: The Limits of Natural Language

### The Structural Limits of Natural Language

Natural language has remarkable expressive power and flexibility for human
communication. That flexibility is also exactly what makes it problematic for
precise system description. Natural language contains unavoidable structural
ambiguity.

- **Lexical ambiguity**: the same word has multiple meanings  
  Example: "bank" (financial institution vs. river bank), "log" (record vs.
  timber)
- **Syntactic ambiguity**: a sentence can be parsed in multiple ways  
  Example: "old male and female doctors"
- **Semantic ambiguity**: the meaning of a sentence can be interpreted in
  multiple ways  
  Example: "Customers may return products" (until when? under what conditions?
  in what state?)
- **Pragmatic ambiguity**: interpretation depends on context  
  Example: "within an appropriate amount of time" (the standard for
  "appropriate" varies by system)

### Concrete Examples of Ambiguity in Specifications

Consider concrete examples drawn from software specifications.

**Example 1**: "The system validates user input."

- What input is covered? All input, or only certain kinds?
- What kind of validation is meant? Format checks, content checks, or both?
- When is validation performed? At entry time, at submission time, or later?
- What happens if validation fails?

**Example 2**: "If the database connection fails, the system handles the error
appropriately."

- What counts as failure? Timeout, authentication error, or network outage?
- What is "appropriate handling"? Retry, fallback, or user notification?
- How long may the system spend handling the error?

**Example 3**: "The system provides high performance."

- How high is "high"? Relative to another system or against an absolute
  threshold?
- Which operation's performance matters? Response time or throughput?
- Under what conditions? Normal load, peak load, or failure mode?

### Practical Problems Caused by Ambiguity

These ambiguities are not just theoretical concerns. They cause concrete
problems in real projects.

- **Different interpretations inside the development team**: front-end
  developers, back-end developers, and testers read the same specification and
  understand different things.
- **Misalignment with the customer**: an implementation the team considers
  correct does not match the customer's expectations.
- **Test-case mismatch**: the tester's interpretation differs from the
  implementer's interpretation, so testing no longer validates the real
  requirement.
- **Confusion during maintenance**: after the original developers leave, new
  developers interpret the specification differently and introduce unintended
  changes.

### Quantitative Analysis of Ambiguity

Interestingly, ambiguity in specification documents can be measured
quantitatively. By applying techniques from linguistic ambiguity analysis, it
is possible to estimate the density of ambiguous expressions in a document.

![Figure 3-1: Hierarchy of ambiguity in specification writing and the improvement provided by formalization]({{ '/assets/images/diagrams/specification-ambiguity-hierarchy.svg' | relative_url }})

According to research on typical software requirements specifications:

- there are, on average, 15 to 20 ambiguous expressions per page;
- about 30% of important functional requirements allow multiple
  interpretations; and
- about 50% of non-functional requirements lack quantitative criteria.

These numbers reveal a structural limit of specification writing based only on
natural language.

![Figure 3-2: Levels of specification precision and their effect on reducing cognitive load]({{ '/assets/images/diagrams/specification-precision-levels.svg' | relative_url }})

### Conventional Approaches to Resolving Ambiguity and Their Limits

Software engineering has developed various approaches for dealing with the
ambiguity of natural language.

- **Structured documents**: describe requirements through templates or fixed
  forms  
  Advantage: they improve consistency to some degree  
  Limitation: they do not eliminate ambiguity inside the structure itself
- **Glossaries**: define project-specific terminology  
  Advantage: they partially reduce lexical ambiguity  
  Limitation: the definitions themselves may still be ambiguous
- **Prototypes**: make requirements concrete through a working simplified
  version  
  Advantage: they support visual and experiential understanding  
  Limitation: exceptional cases and internal behavior often remain unclear
- **Review meetings**: confirm interpretations among stakeholders  
  Advantage: they use human knowledge and experience  
  Limitation: participants vary in understanding and attention

These approaches are useful, but they do not solve the root problem.
Completely eliminating ambiguity requires a stricter approach.

### Motivation for Formal Description

This ambiguity problem is one of the strongest motivations for formal
specification. By using mathematical notation, we can describe system behavior
in a way that leaves no room for interpretation.

That said, formal description also has limits.

- Not every requirement can be formalized.
- Formalization requires time and skill.
- Not every stakeholder can read a formal notation directly.

In real projects, the practical approach is therefore to combine natural
language and formal notation appropriately. Critical parts can be described
formally, while other parts remain in natural language. That staged approach is
both realistic and effective.

## 3.3 Preconditions and Postconditions: Contracts for Operations

### The Power of the Contract Concept

Viewing a function or operation as a contract is one of the foundational ideas
of formal specification. The idea is inspired by contracts in everyday life.

Consider a commercial contract. "The seller provides product A. The buyer pays
amount B. The product is delivered by date C." This contract has a clear
structure.

- **Preconditions**: conditions under which the contract can take effect
  (the product exists, the buyer is able to pay)
- **Obligations**: actions each party must perform
- **Guarantees**: results that are ensured once the contract is performed

Program operations can be described using exactly the same structure.

### Preconditions: Assumptions of an Operation

A precondition is a condition that must hold for an operation to work
correctly. It defines the range within which the operation makes its promise.

Consider an operation that retrieves an element from an array.

Pseudo notation:

```text
operation get_element(array, index)
precondition:
  - array is not null
  - 0 ≤ index < length(array)
```

This precondition defines the caller's responsibility. If the caller invokes
the operation without satisfying these conditions, the behavior of the
operation is no longer guaranteed.

Designing preconditions involves an important trade-off.

- **Strict preconditions**: simplify the implementation, but increase the
  burden on the caller
- **Lenient preconditions**: make the operation easier to use, but make the
  implementation more complex

That trade-off reflects the overall design philosophy of the system. Defensive
programming tends to prefer lenient preconditions, while Design by Contract
usually prefers stricter ones.

### Postconditions: Guarantees of an Operation

A postcondition is a condition that must hold after an operation completes. It
defines the value the operation promises to provide.

Continuing the array element retrieval example:

Pseudo notation:

```text
operation get_element(array, index) → result
precondition:
  - array is not null
  - 0 ≤ index < length(array)
postcondition:
  - result = array[index]
  - array is unchanged
```

A postcondition defines the implementer's responsibility. An implementation
that fails to satisfy it violates the contract.

When writing postconditions, it is important to state both what changes and
what does not change. In this example, the specification guarantees not only
that the returned value is correct, but also that the array itself remains
unchanged.

### The Frame Problem: What Does Not Change?

The frame problem in programming is the problem of describing explicitly what
an operation does *not* modify. The issue was first recognized in artificial
intelligence, but it also matters deeply in software specification.

Consider an operation that withdraws money from a bank account.

Pseudo notation:

```text
operation withdraw(account, amount)
precondition:
  - account.balance ≥ amount
  - amount > 0
postcondition:
  - account.balance = old(account.balance) - amount
  - account.number is unchanged
  - account.owner is unchanged
  - all other accounts are unchanged
```

The clause "all other accounts are unchanged" makes explicit that this
operation does not affect other accounts. Such non-modification guarantees are
essential for predictability.

### Exceptional Postconditions

In real systems, an operation does not always complete normally. Network
failures, resource shortages, and unexpected input are common sources of
exceptional behavior.

These cases can also be described as postconditions.

Pseudo notation:

```text
operation transfer_money(from_account, to_account, amount)
precondition:
  - from_account.balance ≥ amount
  - amount > 0
normal postcondition:
  - from_account.balance = old(from_account.balance) - amount
  - to_account.balance = old(to_account.balance) + amount
exceptional postcondition (network_failure):
  - all accounts unchanged
  - failure_log updated
exceptional postcondition (insufficient_funds):
  - all accounts unchanged
  - error_count incremented
```

By stating exceptional postconditions explicitly, we can specify error-handling
requirements formally as well.

### Contract Inheritance and Overriding

In object-oriented programming, the relationship among contracts in an
inheritance hierarchy is an important design principle. The Liskov Substitution
Principle can be understood in exactly these contractual terms.

When a subclass overrides a method:

- the precondition may be weakened, or remain the same;
- the postcondition may be strengthened, or remain the same.

This guarantees that code written against the parent class contract can still
work correctly when given an instance of the child class.

### Practicing Design by Contract

The contract concept is useful in practical programming as well. Eiffel treats
contracts as a first-class language feature. Java and C# can express contracts
through language features or libraries. Python can also express them through a
library or through a minimal approach based on `assert`.

```python
def withdraw(account, amount):
    assert amount > 0
    assert account.balance >= amount
    old_balance = account.balance
    account.balance -= amount
    assert account.balance == old_balance - amount
```

Such contract checks help detect violations at runtime and are useful in
debugging and testing. In Python, however, `assert` statements themselves are
skipped when the interpreter runs with optimization enabled, for example
through `python -O`. If you need reliable contract enforcement in production,
it is better to check conditions with `if` statements and raise explicit
exceptions, or to use a contract library such as `icontract`.

## 3.4 Invariants: The System's Standing Promises

### The Essential Meaning of Invariants

An invariant is a property that the system must always satisfy. It is one of
the system's basic promises and a constraint that must not be broken by any
valid operation.

A useful analogy from the physical world is conservation of energy. Whatever
physical process occurs, the total amount of energy is preserved. Software
systems likewise have properties that should remain true regardless of which
operation is performed.

Invariants are a way of guaranteeing consistency. They appear at many levels,
including database integrity constraints, object-state constraints, and
system-wide resource constraints.

### Data Invariants

The most basic invariants are constraints at the level of data structures.

**Invariant for an array**:

Pseudo notation:

```text
invariant: 0 ≤ length ≤ capacity
invariant: ∀i ∈ [0, length). elements[i] is valid
```

**Invariant for a linked list**:

Pseudo notation:

```text
invariant: head = null ⇒ size = 0
invariant: head ≠ null ⇒ reachable_nodes(head) = size
invariant: ∀node. node.next ≠ null ⇒ node ≠ node.next (no self-loops)
```

**Invariant for a binary search tree**:

Pseudo notation:

```text
invariant: ∀node.
  (node.left ≠ null ⇒ node.left.value < node.value) ∧
  (node.right ≠ null ⇒ node.value < node.right.value)
```

These invariants must be preserved by all operations on the data structure,
such as insertion, deletion, and update.

### Business Invariants

At a higher level, invariants reflect business rules.

**Inventory-management system**:

Pseudo notation:

```text
invariant: ∀product. product.stock_count ≥ 0
invariant: ∀product. product.reserved_count ≤ product.stock_count
invariant: sum(all_orders.quantities) = sum(all_products.reserved_count)
```

**Banking system**:

Pseudo notation:

```text
invariant: ∀account. account.balance ≥ account.minimum_balance
invariant: sum(all_accounts.balance) = total_deposits - total_withdrawals
invariant: ∀transaction. transaction.from_amount = transaction.to_amount
```

**User-management system**:

Pseudo notation:

```text
invariant: ∀user. user.email ≠ null ∧ is_valid_email(user.email)
invariant: ∀user. count(users_with_email(user.email)) = 1
invariant: ∀session. session.user ≠ null ⇒ user.is_active
```

### System Invariants

Important invariants also exist at the level of the entire system.

**Resource management**:

Pseudo notation:

```text
invariant: allocated_memory ≤ total_memory
invariant: active_connections ≤ max_connections
invariant: cpu_usage ≤ 100%
```

**Security**:

Pseudo notation:

```text
invariant: ∀operation. requires_authentication(operation) ⇒ current_user.is_authenticated
invariant: ∀data. data.classification = "secret" ⇒ current_user.clearance_level ≥ SECRET
```

**Consistency**:

Pseudo notation:

```text
invariant: ∀replica. replica.data = master.data (eventually)
invariant: ∀cache_entry. cache_entry.timestamp ≤ current_time
```

### The Layered Nature of Invariants

In complex systems, invariants are also hierarchical. Higher-level invariants
rest on lower-level ones.

Pseudo notation:

```text
Level 1 (data structure): array bounds are respected
Level 2 (object): account balances are never negative
Level 3 (business): total balances are conserved
Level 4 (system): the overall security policy is preserved
```

This structure makes it possible to use the right abstraction at each level
while still preserving overall consistency.

### Verifying Invariants

To confirm that invariants are actually preserved, we must verify them against
all operations.

- **Static verification**: prove, before execution, that the invariant holds on
  every possible execution path.
- **Dynamic verification**: check the invariant at runtime and detect
  violations.
- **Formal verification**: prove invariant preservation rigorously by
  mathematical reasoning.

### Principles for Designing Invariants

Good invariant design follows several principles.

- **Minimality**: include only the constraints that are necessary.
- **Independence**: avoid redundancy with other invariants.
- **Verifiability**: make the invariant efficient to check.
- **Understandability**: keep the invariant understandable to domain experts.
- **Stability**: ensure that the invariant remains meaningful as the system
  evolves.

### Handling Invariant Violations

It is also important to define a strategy for what to do when an invariant
violation is detected.

- **Prevention**: forbid operations that could create a violation.
- **Detection**: detect violations as early as possible.
- **Recovery**: restore the system from an invalid state to a valid one.
- **Reporting**: analyze causes and feed them back into improvement.

## 3.5 Learning Through an Example: Fully Specifying a Stack

### An Informal Understanding of a Stack

A stack is one of the most fundamental data structures in programming. It
manages elements according to the principle of LIFO (Last In, First Out).
Piles of books or stacks of dishes are everyday examples.

Most people understand the behavior of a stack intuitively. By translating that
intuition into a formal specification, however, we can remove ambiguity and
make correctness easier to guarantee.

### Basic Operations on a Stack

A stack usually provides the following operations.

- `create()`: create an empty stack
- `push(item)`: add an item to the top of the stack
- `pop()`: remove the top item from the stack and return it
- `top()`: return the top item without removing it
- `isEmpty()`: test whether the stack is empty
- `size()`: return the number of items in the stack

Let us specify these operations formally.

### Formal Representation of State

First, we represent the state of a stack mathematically.

Pseudo notation:

```text
Stack[T] = ⟨items: Sequence[T], capacity: ℕ⟩

where:
  T: element type
  items: ordered sequence of elements (items[0] is the top)
  capacity: maximum size of the stack
```

Invariants:

Pseudo notation:

```text
invariant: |items| ≤ capacity
invariant: capacity > 0
```

### Specification of `create`

Pseudo notation:

```text
operation create(cap: ℕ) → Stack[T]
precondition:
  cap > 0
postcondition:
  result.items = ⟨⟩
  result.capacity = cap
```

This specification is clear. If the operation is called with a positive
capacity, it creates an empty stack.

### Specification of `push`

Pseudo notation:

```text
operation push(stack: Stack[T], item: T) → Stack[T]
precondition:
  |stack.items| < stack.capacity
postcondition:
  result.items = ⟨item⟩ ∘ stack.items
  result.capacity = stack.capacity
  |result.items| = |stack.items| + 1
```

Here `∘` denotes sequence concatenation. The precondition states that `push` is
not defined for a full stack.

### Specification of `pop`

Pseudo notation:

```text
operation pop(stack: Stack[T]) → (Stack[T], T)
precondition:
  |stack.items| > 0
postcondition:
  stack.items = ⟨top_item⟩ ∘ result.0.items
  result.1 = top_item
  result.0.capacity = stack.capacity
  |result.0.items| = |stack.items| - 1
```

This specification returns a pair consisting of the new stack and the item that
was removed.

### Specification of `top`

Pseudo notation:

```text
operation top(stack: Stack[T]) → T
precondition:
  |stack.items| > 0
postcondition:
  result = stack.items[0]
  stack is unchanged
```

Because `top` does not modify the stack, the frame condition explicitly states
that the stack is unchanged.

### Specification of `isEmpty`

Pseudo notation:

```text
operation isEmpty(stack: Stack[T]) → Boolean
precondition:
  true
postcondition:
  result = (|stack.items| = 0)
  stack is unchanged
```

### Specification of `size`

Pseudo notation:

```text
operation size(stack: Stack[T]) → ℕ
precondition:
  true
postcondition:
  result = |stack.items|
  stack is unchanged
```

### Relationships Among Operations

Not only the specifications of individual operations matter, but also the
relationships among them.

**Relationship between `push` and `pop`**:

Pseudo notation:

```text
∀s: Stack[T], x: T.
  |s.items| < s.capacity ⇒
  pop(push(s, x)) = (s, x)
```

**Relationship between `push` and `top`**:

Pseudo notation:

```text
∀s: Stack[T], x: T.
  |s.items| < s.capacity ⇒
  top(push(s, x)) = x
```

**Relationship between `isEmpty` and `size`**:

Pseudo notation:

```text
∀s: Stack[T].
  isEmpty(s) ⟺ (size(s) = 0)
```

### Error-Handling Specification

In real systems, we also need to define behavior when a precondition is
violated.

Pseudo notation:

```text
operation pop_safe(stack: Stack[T]) → (Stack[T], Option[T])
precondition:
  true
postcondition:
  |stack.items| > 0 ⇒
    (result.0, result.1) = (pop(stack), Some(top(stack)))
  |stack.items| = 0 ⇒
    (result.0, result.1) = (stack, None)
```

### Specifying Performance Characteristics

A formal specification can also include performance requirements.

Pseudo notation:

```text
performance characteristics:
  push: O(1) time, O(1) space
  pop: O(1) time, O(1) space
  top: O(1) time, O(1) space
  isEmpty: O(1) time, O(1) space
  size: O(1) time, O(1) space
```

### Considering Concurrent Access

In a multithreaded environment, the specification may also need to address
concurrency.

Pseudo notation:

```text
concurrency specification:
  - concurrent read operations (top, isEmpty, size) are safe
  - write operations (push, pop) require mutual exclusion
  - results of read operations during a write operation are undefined
```

### Checking Specification Completeness

The following checklist helps determine whether the specification is complete.

1. **Operation coverage**: are all required operations defined?
2. **State-transition coverage**: are all valid state transitions possible?
3. **Error-case coverage**: are all abnormal cases handled?
4. **Invariant preservation**: do all operations preserve the invariants?
5. **Operational relationships**: do the expected relationships among
   operations hold?

A specification like this gives implementers a clear target, gives testers a
basis for comprehensive test design, and gives users a precise understanding of
how to use the data structure correctly.

---

## End-of-Chapter Exercises

### Basic Exercise 1: Identifying Ambiguity

Identify the ambiguous parts of the following natural-language specification and
list the possible interpretations for each of them.

"After logging in to the system, the user can upload a file. Uploaded files are
scanned for viruses appropriately, and if no problem is found, they are saved.
Files that are too large or invalid are rejected."

1. Identify the ambiguous expressions in each sentence.
2. For each expression, provide at least two different interpretations.
3. Explain how each ambiguity could affect the implementation.

### Basic Exercise 2: Writing a Contract

Write formal preconditions and postconditions for the following function.

```python
def binary_search(sorted_array, target):
    """
    Search for a target value in a sorted array.
    Return its index if found.
    Return -1 if not found.
    """
```

What should be described:

1. Preconditions (the state of the array, constraints on arguments, and so on)
2. Postconditions in the normal case (return value, state of the array, and so
   on)
3. Postconditions in exceptional cases, if applicable
4. Frame conditions describing what does not change

### Practical Exercise 1: Specifying a Queue

Following the stack example, create a complete specification for a queue
(first-in, first-out data structure).

1. Formal representation of state
2. Specifications of the basic operations (`enqueue`, `dequeue`, `front`,
   `isEmpty`, and `size`)
3. Data invariants
4. Relationships among operations
5. Error-handling considerations

### Practical Exercise 2: Invariants for an Email System

Consider a simple email system and define invariants for the following
components.

System elements:

- Users (`id`, email address, password)
- Mailboxes (inbox, sent box, trash)
- Messages (sender, recipient, subject, body, timestamp)

Required invariants:

1. At least three invariants related to data consistency
2. At least two invariants related to security
3. At least two invariants related to business rules

### Advanced Exercise: Validating a Specification

For the queue specification you created, perform the following checks.

1. **Consistency check**: does any contradiction arise from combining
   different operations?
2. **Completeness check**: are all expected usage patterns covered?
3. **Implementability check**: is an efficient implementation satisfying the
   specification possible?
4. **Test strategy**: what test cases are required if testing is derived from
   this specification?

Working through these exercises should build practical skill in formal
specification writing. The next chapter introduces Alloy as a concrete tool and
shows how to automate parts of specification analysis and verification.
