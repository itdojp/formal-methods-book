# Appendix A: Mathematics Refresher

This appendix collects the minimum set of mathematical notation that appears repeatedly in this book as a quick reference. It is not intended to be a full set of lecture notes. It is a cheat sheet for reading the main chapters and writing specifications, especially Chapter 4 on Alloy, Chapter 5 on Z, Chapter 6 on CSP, and Chapter 7 on TLA+.

Notation differs across traditions and tools even when the underlying concept is the same. To avoid inconsistent notation inside this book, also refer to Appendix C, which records notation differences for the English edition and is being expanded into a fuller cross-reference.

## A.1 Sets

A set represents a collection of elements. In specification writing, sets are the basic unit used to represent states and the range of values that are allowed.

Common symbols:
- Membership: `x ∈ A` (`x` is an element of `A`), `x ∉ A`
- Subset: `A ⊆ B` (`A` is included in `B`), `A ⊂ B` (proper subset)
- Empty set: `∅`
- Set operations: `A ∪ B` (union), `A ∩ B` (intersection), `A \ B` (difference)
- Power set: `ℙ X` (the set of all subsets of `X`)
- Cartesian product: `X × Y` (the set of ordered pairs)
- Cardinality: `#A` (the number of elements in `A`)

Example:
```text
A = {1, 2, 3}
B = {3, 4}

1 ∈ A
A ∩ B = {3}
A \ B = {1, 2}
```

## A.2 Logic

Constraints in specifications are written as logical formulas, including invariants, preconditions, and postconditions.

Connectives, which combine propositions:
- Negation: `¬P` (not `P`)
- Conjunction: `P ∧ Q` (`P` and `Q`)
- Disjunction: `P ∨ Q` (`P` or `Q`)
- Implication: `P ⇒ Q` (if `P`, then `Q`)
- Equivalence: `P ⇔ Q` (`P` and `Q` are equivalent)

Quantifiers, which express “for all” and “there exists”:
- Universal quantification: `∀x : X • P(x)` (for every `x` in `X`, `P(x)` holds)
- Existential quantification: `∃x : X • P(x)` (there exists some `x` in `X` such that `P(x)` holds)

Example: “The balance of every account is non-negative.”
```text
∀a : Account • balance(a) ≥ 0
```

## A.3 Relations and Functions

A relation represents a correspondence between elements of two sets. A mapping, or function, is a special case of a relation.

### Relations

A relation `R` can be understood as a subset of `X × Y`:
```text
R ⊆ X × Y
```

In Z notation, the following type is used:
- `R : X ↔ Y` (a relation between `X` and `Y`)

Common operations:
- Domain: `dom R` (the elements that appear on the `X` side)
- Range: `ran R` (the elements that appear on the `Y` side)

### Functions

A mapping, or function, is a relation in which each input has a unique output.

In this book, the following minimum set is used:
- Total function: `f : X → Y` (a value is defined for every element of `X`)
- Partial function: `f : X ⇸ Y` (the value may be undefined for some elements)

Example: some books do not have a due date assigned.
```text
dueDate : Book ⇸ Date
```

## A.4 State, Operations, and Invariants

In specifications, the state and the operations are described separately.

A minimal picture:
- State: the data held by the system, such as sets, relations, and functions
- Invariant: a constraint that must always hold
- Operation: a procedure that updates the state, described with preconditions, postconditions, and frame conditions

Example: a conceptual view of a bank-account constraint
```text
State: balance : Account → Int
Invariant: ∀a : Account • balance(a) ≥ 0
Operation: withdraw(a, amount)
  Pre: amount > 0 ∧ balance(a) ≥ amount
  Post: balance'(a) = balance(a) - amount
```

## A.5 Equivalence Relations and Induction (Minimum Required)

### Equivalence relations

An equivalence relation `~` is a relation that satisfies the following three properties:
- Reflexivity: `∀x • x ~ x`
- Symmetry: `∀x, y • x ~ y ⇒ y ~ x`
- Transitivity: `∀x, y, z • x ~ y ∧ y ~ z ⇒ x ~ z`

Equivalence relations are used when we want to treat multiple things as “the same,” for example when dealing with identifiers, normalization, or abstraction.

### Induction

Induction is a basic method for proving properties over natural numbers or over steps in a sequence. In its minimal form, it has two stages:
1. Base case: show `P(0)`
2. Inductive step: show `P(n) ⇒ P(n+1)`

In discussions of state transitions, induction is useful as an auxiliary line of reasoning when explaining invariants in the form “it holds up to step `n`, therefore it also holds at step `n+1`.”
