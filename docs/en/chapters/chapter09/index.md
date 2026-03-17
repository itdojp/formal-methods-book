---
layout: book
title: "Chapter 9: Fundamentals of Theorem Proving"
locale: "en"
lang: "en"
source_path: "src/en/chapters/chapter09.md"
---
# Chapter 9: Fundamentals of Theorem Proving

## 9.1 Mechanizing Proof: Cooperation Between Mathematicians and Computers

### Proof as a Human Intellectual Activity

Mathematical proof is one of the highest forms of human intellectual activity.
From Euclid in ancient Greece to modern mathematicians, truth has been
established through rigorous logical reasoning. But are mathematical proofs
fully trustworthy in practice?

History shows that even famous mathematicians have published incorrect proofs.
The 1976 proof of the Four Color Theorem by Appel and Haken relied on massive
computer-assisted case analysis. That result shocked the mathematical
community, in part because no human could feasibly inspect every case in full
detail.

Today, mathematical proofs are even more complex. Classification theorems,
Fermat's Last Theorem, and the proof of the Poincaré conjecture each span
hundreds of pages, and only a small number of specialists can claim full
understanding of the whole argument. Human cognition is now a serious
bottleneck.

### Why Machine-Based Proof Checking Is Necessary

This challenge is even more severe in software verification. Proving the
correctness of practical software requires reasoning about huge numbers of
details. Doing all of that manually is not realistic.

*Proof checking* addresses this limit. Humans design the high-level proof
strategy, and machines verify the details. This combines human creativity with
machine precision.

### The Basic Idea of a Proof Assistant

A *proof assistant* is a tool that helps users construct and verify
mathematical proofs. It is not merely a calculator. It is a reasoning tool.

The central idea behind modern proof assistants is *type theory*. By extending
the notion of a type system, propositions can be represented as types and
proofs as programs. In that setting, writing a proof and writing a program
become two views of the same act.

```coq
Theorem addition_commutative : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

This theorem proves commutativity of addition over natural numbers. The script
is readable by humans, but it is also formal enough for the machine to check
precisely.

### Complementing Chapter 8 on Model Checking

Theorem proving and model checking are complementary verification methods.
Model checking, as discussed in Chapter 8, offers exhaustive exploration within
finite scopes or finite state spaces. Theorem proving offers mathematical
rigor over infinite domains and general cases.

**Characteristics of model checking**:

- automatic verification
- explicit counterexamples when a property fails
- strong fit for finite-state systems
- comparatively lower learning cost

**Characteristics of theorem proving**:

- mathematical rigor
- support for infinite structures and general statements
- constructive reasoning when desired
- higher learning cost, but stronger guarantees

Used together, they support a broader and more practical verification
strategy.

### The Deeper Meaning of the Curry-Howard Correspondence

The *Curry-Howard correspondence* reveals a deep relationship between logic and
computation:

- **proposition** ↔ **type**
- **proof** ↔ **program**
- **proof normalization** ↔ **program execution**

This is not a loose analogy. Logical inference rules and typing rules for
programs share the same structure.

Example: implication introduction

```text
Logic:
To prove P -> Q, assume P and prove Q.

Type theory:
To construct a value of type P -> Q, define a function that
takes a value of type P and returns a value of type Q.
```

### Constructive Mathematics and Classical Mathematics

Proof assistants often work in a *constructive mathematics* setting. In
constructive reasoning, an existence proof should provide an actual
construction.

**Classical proof**:
"`√2` is irrational." One may prove this by contradiction.

**Constructive proof**:
"Algorithm `A` produces, for every input `n`, an output satisfying property
`P`." The proof defines `A` and then proves its correctness.

Constructive proofs are valuable because usable algorithms can often be
extracted from them.

### The Division of Labor Between Humans and Machines

Effective theorem proving depends on the right division of labor.

**What humans do best**:

- design the overall proof strategy
- discover key lemmas
- choose the right level of abstraction
- provide intuitive understanding

**What machines do best**:

- check detailed inference steps
- handle large case splits
- perform type checking and consistency checking
- automate routine proof search

The goal is not to replace human reasoning, but to combine it with reliable
mechanical checking.

### Establishing Trust

The proof assistant itself must also be trustworthy. If the tool contains a
bug, the proofs it accepts may be unsound.

The standard response is to design a small *trusted kernel*. If the core logic
checker is small and well understood, then it is enough to trust that kernel.
Convenience features can live outside it.

For example, the trusted kernel of Rocq (formerly Coq) is only a few thousand
lines of OCaml, whereas the full system is vastly larger. Tactics and other
automation operate outside the kernel and still have their final result checked
by it.

### Proof Reuse and Accumulation

Another major benefit of mechanized proof is reuse. Once a theorem has been
proved, it can be stored as a library asset and reused elsewhere.

Large formalization projects now exist across major branches of mathematics:

- **mathlib** for Lean, which covers a broad range of modern mathematics
- **Mathematical Components** in the Rocq ecosystem, with a strong focus on
  algebraic structure
- **Archive of Formal Proofs** for Isabelle/HOL, which collects results across
  many areas

These libraries increasingly make it possible to build complex results by
composing previously verified proof assets.

### Impact on Education

Proof assistants can also reshape mathematics education. When students learn
proof with machine support, they can:

- experience rigor directly rather than only reading about it
- inspect each step of a proof explicitly
- detect invalid reasoning immediately
- build complex proofs gradually

Several universities already use proof assistants in mathematics and computer
science courses.

### Use in Industry

Proof assistants are no longer confined to academia. They are beginning to
play serious roles in industry as well:

- **CompCert** proves correctness of a C compiler
- **seL4** proves functional correctness of a microkernel
- **Amazon s2n** uses formal reasoning for parts of a TLS implementation

These examples show that theorem proving is maturing into a practical
engineering technique.

## 9.2 Foundations of Logic: Rules of Inference

### Formal Logic as a Language

Logic studies the rules of valid reasoning. Everyday arguments often contain
ambiguity, rhetoric, or emotion. Formal logic strips those away and focuses on
structure alone. That makes machine-checkable reasoning possible.

Understanding formal logic is essential for using a proof assistant well,
because the assistant's internal reasoning rules are grounded in logic.

### Propositional Logic: The Starting Point

Propositional logic is the most basic layer of logic. It is built from atomic
propositions and logical connectives.

**Basic logical connectives**:

- **∧** (AND): `P ∧ Q`
- **∨** (OR): `P ∨ Q`
- **¬** (NOT): `¬P`
- **→** (IMPLIES): `P → Q`
- **↔** (IF AND ONLY IF): `P ↔ Q`

Their meanings are completely defined by truth tables:

```text
P | Q | P∧Q | P∨Q | P→Q | P↔Q
--+---+-----+-----+-----+-----
T | T |  T  |  T  |  T  |  T
T | F |  F  |  T  |  F  |  F
F | T |  F  |  T  |  T  |  F
F | F |  F  |  F  |  T  |  T
```

### Natural Deduction: Formalizing Human-Style Reasoning

*Natural deduction*, developed by Gerhard Gentzen, is a proof system designed
to mirror how humans naturally reason while remaining formally precise.

**Implication introduction (`→I`)**:

```text
[P]
 ⋮
 Q
---
P→Q
```

"If Q can be proved under the assumption P, then P → Q holds."

**Implication elimination (`→E`, modus ponens)**:

```text
P→Q  P
------
  Q
```

"If P → Q and P are both established, then Q follows."

**Conjunction introduction (`∧I`)**:

```text
P  Q
----
P∧Q
```

**Conjunction elimination (`∧E`)**:

```text
P∧Q     P∧Q
----  or ----
 P        Q
```

### The Structure of Proofs: Proof Trees

In natural deduction, a proof can be viewed as a *proof tree*. Leaves are
assumptions or axioms, internal nodes are rule applications, and the root is
the conclusion being proved.

Example: a proof of `((P→Q)∧(Q→R))→(P→R)`

```text
[P→Q]¹  [P]³   [Q→R]¹  [P→Q]¹  [P]³
------------- ----------------------
      Q                Q       [Q→R]¹
      -------------------------
                   R
                 -----
                 P→R                 ³
           ------------------
           (P→Q)∧(Q→R)→(P→R)         ¹
```

This proof tree captures a syllogistic pattern precisely.

### Predicate Logic: A More Expressive Logic

Propositional logic treats whole propositions as indivisible units. Real
mathematical reasoning requires quantification:

- "for every natural number `n`"
- "there exists a real number `x`"

First-order predicate logic extends propositional logic with quantifiers:

- **universal quantifier** `∀x. P(x)` meaning "for all `x`, `P(x)`"
- **existential quantifier** `∃x. P(x)` meaning "there exists an `x` such that
  `P(x)`"

Examples:

- `∀n:ℕ. even(n) ∨ odd(n)`
- `∃x:ℝ. x² = 2`

### Inference Rules for Quantifiers

**Universal introduction (`∀I`)**:

```text
P(a)  (a is fresh)
------------------
     ∀x. P(x)
```

"If `P(a)` is proved for an arbitrary fresh element `a`, then `∀x. P(x)`."

**Universal elimination (`∀E`)**:

```text
∀x. P(x)
--------
  P(t)
```

"From `∀x. P(x)`, instantiate any term `t`."

**Existential introduction (`∃I`)**:

```text
P(t)
--------
∃x. P(x)
```

**Existential elimination (`∃E`)**:

```text
∃x. P(x)  [P(a)]
            ⋮     (a is fresh)
            Q
-----------------
        Q
```

### Reasoning with Equality

Equality is central in mathematics and program verification. It satisfies the
familiar principles:

**Reflexivity**:

```text
-------
t = t
```

**Symmetry**:

```text
t₁ = t₂
-------
t₂ = t₁
```

**Transitivity**:

```text
t₁ = t₂  t₂ = t₃
---------------
    t₁ = t₃
```

**Substitution**:

```text
t₁ = t₂  P(t₁)
-------------
    P(t₂)
```

### Extending to Higher-Order Logic

In first-order logic, quantification ranges only over individuals. In
mathematics, however, we often want to quantify over functions and predicates
as well.

*Higher-order logic* supports that style of reasoning:

【擬似記法】
```coq
Definition continuous (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f(x) - f(y)| < ε.

Theorem exists_continuous_function : ∃ f : ℝ → ℝ, continuous f.
```

### Type Theory: Unifying Logic and Computation

Many modern proof assistants use *type theory* as their logical foundation. In
type theory, propositions and types are unified, which makes many mathematical
concepts easier to represent directly.

**Dependent types**:

```coq
Definition Vector (A : Type) (n : nat) : Type :=
  { l : list A | length l = n }.

Definition head {A : Type} {n : nat} (v : Vector A (S n)) : A :=
  match v with
  | exist _ (x :: _) _ => x
  end.
```

The length of the vector is part of its type. The type system therefore
guarantees that `head` is only applied to non-empty vectors.

### Soundness and Completeness of Inference Rules

Any logical system is judged by two major meta-properties:

- **soundness**: everything provable in the system is true
- **completeness**: everything true in the intended semantics is provable in
  the system

In proof assistants, soundness is especially important. If the system can prove
something false, then the entire trust argument collapses.

### Intuitionistic Logic and Classical Logic

Proof assistants often adopt *intuitionistic logic*, which is more restrictive
than classical logic.

Main differences include:

- **law of excluded middle**: classical logic accepts `P ∨ ¬P` universally;
  intuitionistic logic does not
- **double-negation elimination**: classical logic derives `P` from `¬¬P`;
  intuitionistic logic generally does not

The practical benefit of intuitionistic logic is that proofs carry
computational content. Existence proofs can often be turned into actual
construction procedures.

### How Logic Appears in a Proof Assistant

It is useful to see how abstract inference rules appear in actual proof
assistant syntax.

Example in Rocq:

```coq
Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  apply HPQ.
  exact HP.
Qed.
```

This proof corresponds directly to implication elimination. `intros` introduces
assumptions, `apply` uses an implication, and `exact` supplies a matching
proof term.

With a strong grasp of these logical foundations, proof-assistant usage
becomes much more systematic and effective.

## 9.3 Type Theory: Unifying Programs and Proofs

### The Evolution of the Concept of a Type

In early programming languages, a type was mostly a description of memory
layout. Type theory transformed that idea. A type became a way to express
logical properties of programs.

In modern type theory, types and programs are deeply linked. Writing a correct
program and proving a theorem become instances of the same general activity.
This is one of the most elegant unifications in computer science.

### The Simply Typed Lambda Calculus

The starting point for type theory is the simply typed lambda calculus. It
extends a calculus of first-class functions with a type system.

**Basic types**:

- base types such as `Bool`, `Nat`, and `String`
- function types `A → B`

**Examples of typed lambda expressions**:

```text
id : A → A = λx:A. x
compose : (B → C) → (A → B) → (A → C)
        = λf:B→C. λg:A→B. λx:A. f(g(x))
```

This system enjoys the important property that well-typed programs do not go
wrong in basic execution terms.

### The Curry-Howard Correspondence in More Detail

The Curry-Howard correspondence can be expressed concretely as follows:

```text
Logic                Type theory
P ∧ Q        ↔      P × Q        (product type)
P ∨ Q        ↔      P + Q        (sum type)
P → Q        ↔      P → Q        (function type)
⊤ (true)     ↔      Unit         (unit type)
⊥ (false)    ↔      Empty        (empty type)
∀x:A. P(x)   ↔      (x:A) → P(x) (dependent function type)
∃x:A. P(x)   ↔      (x:A) × P(x) (dependent pair type)
```

And on the proof/program side:

```text
Logical reasoning             Program construction
Introduce P ∧ Q      ↔        construct a pair (p, q)
Eliminate P ∧ Q      ↔        project fst(pair), snd(pair)
Introduce P → Q      ↔        λ-abstraction λx:P. body
Eliminate P → Q      ↔        function application f(argument)
```

### Dependent Types: A Revolution in Expressiveness

A *dependent type* is a type that depends on a value. This lets us express
program properties directly at the type level.

Example: vectors indexed by length

```coq
Inductive vec (A : Type) : nat → Type :=
| vnil : vec A 0
| vcons : ∀ n, A → vec A n → vec A (S n).

Definition head {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v with
  | vcons _ x _ => x
  end.
```

Here, `head` can only be applied to vectors of length `S n`, that is, to
non-empty vectors. The type system rules out the empty case before execution.

### Inductive Types: Representing Data Structures

Inductive types define recursive data structures.

**Natural numbers**:

```coq
Inductive nat : Type :=
| O : nat
| S : nat → nat.
```

This states that a natural number is either zero or the successor of another
natural number.

**Lists**:

```coq
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A → list A → list A.
```

**Binary trees**:

```coq
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : A → tree A → tree A → tree A.
```

### The Principle of Induction

From inductive definitions, proof assistants automatically generate induction
principles.

**Induction on natural numbers**:

```coq
nat_ind : ∀ P : nat → Prop,
  P 0 →                           (* base case *)
  (∀ n, P n → P (S n)) →         (* inductive step *)
  ∀ n, P n                       (* conclusion *)
```

**Induction on lists**:

```coq
list_ind : ∀ (A : Type) (P : list A → Prop),
  P nil →
  (∀ (a : A) (l : list A), P l → P (cons a l)) →
  ∀ l : list A, P l
```

These principles are the formal basis of many recursive proofs.

### Equality Type: Representing Identity

An *equality type* expresses the fact that two values are equal.

```coq
Inductive eq (A : Type) (x : A) : A → Prop :=
| eq_refl : eq A x x.

Notation "x = y" := (eq _ x y).
```

With this definition, a proof of `x = y` is built directly only when `x` and
`y` are definitionally the same, and other equalities are proved through
reasoning steps.

### Dependent Pattern Matching

When pattern matching over dependently typed data, the result type can vary by
branch.

```coq
Definition vector_case {A : Type} {n : nat} (v : vec A n) :
  match n with
  | 0 => unit
  | S _ => A
  end :=
  match v with
  | nil _ => tt
  | cons _ _ x _ => x
  end.
```

Here the return type depends on `n`: it is `unit` for length 0 and `A` for a
non-empty vector.

### Proof Relevance

Type theory raises the question of whether two proofs of the same proposition
should be considered distinguishable.

**Proof irrelevance**:

```coq
Axiom proof_irrelevance : ∀ (P : Prop) (p1 p2 : P), p1 = p2.
```

This states that all proofs of the same proposition are equal.

**Proof relevance**:
In some settings, different proofs are distinguished and may carry different
computational meaning.

### Universe Hierarchy

Type theory must also represent *types of types*. That leads to a hierarchy of
universes:

```text
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

Examples:

```coq
nat : Type₀
Type₀ : Type₁
(Type₀ → Type₀) : Type₁
```

This hierarchy prevents paradoxes such as Russell's paradox.

### Constructive Mathematics and Computation

In proof assistants based on type theory, it is often possible to extract
actual executable algorithms from proofs.

【擬似記法】
```coq
Fixpoint gcd (a b : nat) {struct a} : nat :=
  match a with
  | 0 => b
  | S a' => gcd (b mod S a') (S a')
  end.

Theorem gcd_correct : ∀ a b : nat,
  gcd a b = greatest_common_divisor a b.
```

The proof is not only a correctness argument. It is also tied to an executable
algorithm for computing a greatest common divisor.

### Varieties of Type Theory

Several families of type theory are important today.

**Calculus of Constructions**:

- foundational theory behind Rocq
- combines dependent types, polymorphism, and higher-order types

**Martin-Löf type theory**:

- major foundation for constructive mathematics
- emphasizes explicit treatment of identity and constructions

**Homotopy Type Theory**:

- gives equality a geometric interpretation
- introduces the univalence axiom

**Cubical Type Theory**:

- gives a computational presentation of homotopy type theory
- supports computational univalence

### Practical Type Design

In practical proof engineering, type design has direct consequences for
maintainability and safety.

**Error-handling types**:

```coq
Inductive result (A E : Type) : Type :=
| Ok : A → result A E
| Error : E → result A E.
```

**Stateful computation types**:

```coq
Definition State (S A : Type) : Type := S → A × S.
```

**Resource-management types**:

```coq
Inductive linear (A : Type) : Type :=
| use_once : A → linear A.
```

Type theory lets us unify programs and proofs in a way that supports both
mathematical rigor and practical safety.

## 9.4 Practical Work with Proof Assistants

### Rocq (Formerly Coq): A Proof Assistant Based on the Calculus of Constructions

Rocq (formerly Coq) is a proof assistant developed at INRIA in France. It is
based on the Calculus of Constructions and treats mathematical proof and
program development in one framework.

Its main characteristic is that proofs and programs are written in the same
language, and a type checker verifies the proof automatically. This eliminates
entire classes of proof errors that would remain possible in handwritten work.

### Building Basic Proofs

It is useful to begin with very small logical examples.

**Transitivity of implication**:

```coq
Theorem implication_transitivity :
  forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  apply H1.
  exact H3.
Qed.
```

This proof uses:

- `intros` to introduce assumptions
- `apply` to use an implication or a known theorem
- `exact` to provide an already matching proof

**Commutativity of conjunction**:

```coq
Theorem and_commutative : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.
```

The pattern `[HP HQ]` destructures a conjunction into its components.

### Proof by Induction

Mathematical induction is indispensable for proving properties of natural
numbers and recursively defined data.

```coq
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_n : forall n : nat, plus O n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O : forall n : nat, plus n O = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

The `induction` tactic generates the base case and inductive step
automatically.

### Equality and Rewriting

Equality is central in mechanized proof. Rocq supports reasoning by rewriting
with established equalities.

**Associativity of addition**:

```coq
Theorem plus_assoc :
  forall n m p : nat, plus (plus n m) p = plus n (plus m p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

The `rewrite` tactic replaces one side of an equality with the other in the
current goal.

**Commutativity of addition**:

```coq
Lemma plus_n_Sm : forall n m : nat, S (plus n m) = plus n (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, plus n m = plus m n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

In a more complex proof, it is common to prove a helper lemma first and reuse
it in the main theorem.

### Proofs About Lists

Lists are one of the most practical data structures to verify.

```coq
Fixpoint app (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Theorem app_assoc : forall l1 l2 l3 : list nat,
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Fixpoint length (l : list nat) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Theorem app_length : forall l1 l2 : list nat,
  length (app l1 l2) = plus (length l1) (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.
```

### Proofs About Higher-Order Functions

Proof assistants can also handle higher-order functions, that is, functions
that take functions as arguments.

```coq
Fixpoint map (f : nat -> nat) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_app : forall (f : nat -> nat) (l1 l2 : list nat),
  map f (app l1 l2) = app (map f l1) (map f l2).
Proof.
  intros f l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem map_length : forall (f : nat -> nat) (l : list nat),
  length (map f l) = length l.
Proof.
  intros f l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.
```

### Proof Automation

Rocq provides many tactics for automating routine reasoning.

**`auto` and `eauto`**:

```coq
Theorem trivial_example : forall P Q : Prop, P -> P.
Proof.
  auto.
Qed.

Theorem simple_transitivity : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  eauto.
Qed.
```

**`omega` for arithmetic**:

```coq
Require Import Omega.

Theorem arithmetic_example : forall n m : nat,
  n <= m -> n <= m + 1.
Proof.
  intros n m H.
  omega.
Qed.
```

**`tauto` for propositional logic**:

```coq
Theorem propositional_example : forall P Q R : Prop,
  (P /\ Q) -> (P \/ R).
Proof.
  tauto.
Qed.
```

Automation is valuable, but it should be used deliberately. When a proof is
too opaque, debugging and review become harder.

### Type Classes and Structured Proof Development

Type classes help organize proofs and increase reuse.

```coq
Class Monoid (A : Type) := {
  id : A;
  op : A -> A -> A;
  left_id : forall a, op id a = a;
  right_id : forall a, op a id = a;
  assoc : forall a b c, op (op a b) c = op a (op b c)
}.

Instance nat_plus_monoid : Monoid nat := {
  id := 0;
  op := plus;
  left_id := plus_O_n;
  right_id := plus_n_O;
  assoc := plus_assoc
}.
```

This style makes algebraic structure explicit and reusable.

### Extracting Proof Terms

One important feature of Rocq is that executable programs can be extracted from
constructive developments.

```coq
Fixpoint div2 (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => S (div2 n')
  end.

Theorem div2_correct : forall n : nat,
  div2 n <= n /\ n < 2 * div2 n + 2.
Proof.
  intro n.
  induction n as [| n' [IH1 IH2]].
  - split; simpl; auto with arith.
  - destruct n' as [| n''].
    + split; simpl; auto with arith.
    + split; simpl in *; omega.
Qed.

Extraction div2.
```

The extracted program is not a separate implementation invented afterward. It
comes from the same constructive development that established correctness.

### Practical Proof Strategy

Several guidelines help in practice:

1. **Build incrementally**
   - start with simple lemmas
   - decompose complex theorems into smaller pieces
   - check proof progress at each step

2. **Choose induction carefully**
   - match the induction principle to the data structure
   - use strong or mutual induction when appropriate
   - use well-founded induction where necessary

3. **Optimize for readability**
   - choose meaningful lemma names
   - explain the intent of non-obvious steps
   - keep the logical structure visible

4. **Use automation selectively**
   - automate routine fragments
   - keep insight-heavy reasoning explicit
   - prefer proofs that remain debuggable

### Diagnosing and Repairing Errors

During proof development, diagnosing errors correctly is critical.

```coq
Theorem example_with_error : forall n : nat, n + 0 = n.
Proof.
  intro n.
  (* simpl. *) (* If this stays commented out, the proof fails. *)
  reflexivity.
Qed.
```

Understanding type errors, unsolved goals, and missing reductions is a core
skill in proof engineering.

Proof assistants make it possible to combine mathematical rigor with
computational thinking and to produce software artifacts whose correctness
rests on explicit proof.

## 9.5 Proof Strategy and Technique

### A Systematic Approach to Proof Strategy

Proof in a proof assistant is not merely a sequence of tactics. Effective proof
development requires a strategy, a clear understanding of structure, and a
disciplined approach to decomposition.

The process resembles general problem solving or puzzle solving, but the need
for full logical rigor makes the method more systematic.

### Forward Reasoning and Backward Reasoning

Proofs typically combine two major directions of thought.

**Forward reasoning** starts from the assumptions and derives new facts toward
the goal.

```coq
Theorem forward_example : forall n m : nat,
  n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2.
  assert (H3 : n <= m /\ m <= n). { split; [exact H1 | exact H2]. }
  apply Nat.le_antisymm; [exact H1 | exact H2].
Qed.
```

**Backward reasoning** starts from the goal and asks what would be sufficient
to prove it.

```coq
Theorem backward_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

Practical proofs usually alternate between both styles.

### Choosing and Applying Induction

Induction is fundamental, but choosing the right induction variable or
induction structure matters.

**Structural induction**:

```coq
Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => reverse t ++ [h]
  end.

Theorem reverse_involutive : forall l : list nat,
  reverse (reverse l) = l.
Proof.
  intro l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite reverse_app. rewrite IHt. simpl. reflexivity.
Qed.
```

**Strong induction**:

```coq
Require Import Arith.

Theorem strong_induction_example : forall n : nat,
  n >= 2 -> exists a b : nat, a >= 2 /\ b >= 2 /\ n = a * b \/ prime n.
Proof.
  intro n.
  pattern n. apply strong_nat_ind.
Admitted. (* The complete proof is omitted because it is lengthy. *)
```

**Mutual induction**:

```coq
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S n' => odd n'
  end
with odd (n : nat) : bool :=
  match n with
  | O => false
  | S n' => even n'
  end.

Theorem even_odd_exclusive : forall n : nat,
  even n = true -> odd n = false.
Proof.
  intro n.
  functional induction (even n); simpl; auto.
Qed.
```

Choosing the wrong induction principle often makes the proof harder than the
theorem itself.

### Case Analysis and Exhaustiveness

Many proofs depend on a careful case split.

**Logical case analysis**:

```coq
Theorem case_analysis_example : forall n : nat,
  n = 0 \/ n > 0.
Proof.
  intro n.
  destruct n as [| n'].
  - left. reflexivity.
  - right. apply Nat.lt_0_succ.
Qed.
```

**Data-structure case analysis**:

```coq
Theorem list_empty_or_not : forall (A : Type) (l : list A),
  l = nil \/ exists h t, l = h :: t.
Proof.
  intros A l.
  destruct l as [| h t].
  - left. reflexivity.
  - right. exists h, t. reflexivity.
Qed.
```

Exhaustive case analysis is not merely a convenience. It is part of what makes
the proof complete.

### Strategic Use of Lemmas

Complex proofs often become manageable only after introducing the right helper
lemmas.

**A general helper lemma**:

```coq
Lemma app_nil_r : forall (A : Type) (l : list A),
  l ++ nil = l.
Proof.
  intros A l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.
```

**Using the lemma in a main theorem**:

```coq
Theorem reverse_app : forall (A : Type) (l1 l2 : list A),
  reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof.
  intros A l1 l2.
  induction l1 as [| h t IHt].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHt. rewrite app_assoc. reflexivity.
Qed.
```

**Technical lemmas**:

```coq
Lemma S_injective : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H. intro H'. exact H'.
Qed.

Lemma nat_case : forall n : nat, n = 0 \/ exists k, n = S k.
Proof.
  intro n.
  destruct n as [| k].
  - left. reflexivity.
  - right. exists k. reflexivity.
Qed.
```

The right lemma can turn a long proof into a short one.

### Using Reflection and Computation

Rocq can often simplify proof obligations by computation.

**Proof by computation**:

```coq
Example computation_proof : 2 + 3 = 5.
Proof.
  reflexivity.
Qed.

Example boolean_computation :
  let b1 := true in
  let b2 := false in
  b1 && b2 = false.
Proof.
  simpl. reflexivity.
Qed.
```

**Proof by reflection**:

```coq
Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => beq_nat n' m'
  | _, _ => false
  end.

Lemma beq_nat_refl : forall n : nat, beq_nat n n = true.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. exact IHn'.
Qed.

Theorem reflection_example : forall n m : nat,
  beq_nat n m = true -> n = m.
Proof.
Admitted. (* The detailed reflective proof is omitted. *)
```

Reflection lets the proof assistant reduce logical questions to verified
computation, which can be far more efficient.

### Abstraction and Generalization

When a concrete proof pattern appears repeatedly, it is often better to
generalize it.

```coq
Section Parametric_Proofs.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis R_refl : forall x, R x x.
  Hypothesis R_sym : forall x y, R x y -> R y x.
  Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

  Theorem equivalence_relation_property : forall x y z : A,
    R x y -> R y z -> R z x.
  Proof.
    intros x y z Hxy Hyz.
    apply R_sym.
    apply R_trans with y; [exact Hyz | exact Hxy].
  Qed.
End Parametric_Proofs.
```

Parameterization makes proofs reusable and often clarifies what the real
dependencies are.

### Recovering from Errors and Debugging Proofs

When proof development stalls, debugging becomes a skill of its own.

**Diagnosing type errors**:

```coq
Theorem type_error_example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  (* Check (n + 0). *)
  (* Check (@eq nat). *)
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite IHn'. reflexivity.
Qed.
```

**Inspecting proof state**:

```coq
Theorem debugging_example : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  intros n m H1 H2.
  (* Show. *)
  assert (H3 : n <= m /\ m <= n). { split; assumption. }
  (* Show. *)
  apply Nat.le_antisymm; assumption.
Qed.
```

The ability to inspect the current goal, hypotheses, and generated proof term
is essential when proofs become large.

### Optimizing and Refactoring Proofs

Readable proofs matter. Efficient proofs also matter. Those goals are related,
but not identical.

**Compact tactic style**:

```coq
Theorem optimized_proof : forall n : nat, n + 0 = n.
Proof.
  intro n; induction n as [| n' IHn']; simpl;
    [reflexivity | rewrite IHn'; reflexivity].
Qed.
```

**More readable style**:

```coq
Theorem readable_proof : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

**Selective automation**:

```coq
Theorem automated_proof : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n; simpl; [reflexivity | intro; rewrite IHn; reflexivity].
Qed.
```

Good proof engineering means balancing concision, clarity, reuse, and
maintainability.

## 9.6 Practical Program Verification: Tools and Methodology

### The Reality of Theorem Proving in Industry

Theorem proving has moved from pure theory toward practical engineering. It is
now used in domains such as aerospace, automotive systems, finance, and
security, where safety and assurance matter.

Practical program verification, however, differs from proving abstract
mathematical theorems. Real programs involve hardware details, concurrency,
input/output, exceptions, optimization, and implementation constraints.

### CompCert: A Verified C Compiler

CompCert is a fully verified C compiler and one of the landmark achievements in
practical theorem proving.

**CompCert highlights**:

- compilation from a subset of C to several assembly targets
- proof in Rocq of correctness for each compilation phase
- real industrial usage

```coq
Theorem compile_correctness : forall p : C_program,
  well_typed p ->
  forall t : execution_trace,
    C_semantics p t <-> Assembly_semantics (compile p) t.
```

This states that the compiled program preserves the behavior of the source
program.

### seL4: A Verified Microkernel

seL4 is a microkernel whose functional correctness has been proved. It showed
that low-level systems software can be verified at industrially meaningful
scale.

```isabelle
theorem kernel_correctness:
  "system_call_interface ⊆ abstract_specification"

theorem security_properties:
  "∀ p1 p2. isolation(p1, p2) → ¬(p1 can_access data_of p2)"
```

### Layers of Program Verification

Practical verification usually spans multiple abstraction levels.

**1. Algorithm level**:

【擬似記法】
```coq
Fixpoint quicksort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | pivot :: rest =>
    let smaller := filter (fun x => x <=? pivot) rest in
    let larger := filter (fun x => pivot <? x) rest in
    quicksort smaller ++ [pivot] ++ quicksort larger
  end.

Theorem quicksort_correct : forall l : list nat,
  Permutation l (quicksort l) /\ sorted (quicksort l).
```

**2. Data-structure level**:

```coq
Definition binary_search_tree_invariant (t : tree nat) : Prop :=
  forall x left right,
    In_tree x left -> In_tree x right ->
    t = Node x left right ->
    (forall y, In_tree y left -> y <= x) /\
    (forall y, In_tree y right -> x <= y).
```

**3. Memory level**:

```c
/*@ requires \valid(array + (0..n-1));
  @ ensures \forall integer i; 0 <= i < n ==>
  @   \exists integer j; 0 <= j < n && array[i] == \old(array[j]);
  @ ensures sorted(array, 0, n-1);
  */
void sort_array(int *array, int n);
```

Different tools are useful at different layers.

### ACSL: Formal Specification for C

ACSL (ANSI/ISO C Specification Language) is a language for attaching formal
contracts to C programs.

```c
/*@ requires n >= 0;
  @ requires \valid(a + (0..n-1));
  @ ensures \result == \sum(0, n-1, \lambda integer i; a[i]);
  */
int sum_array(int a[], int n) {
  int result = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant result == \sum(0, i-1, \lambda integer k; a[k]);
    @ loop assigns i, result;
    @ loop variant n - i;
    */
  for (int i = 0; i < n; i++) {
    result += a[i];
  }
  return result;
}
```

The contract makes the intended behavior explicit and gives automated tools a
precise target.

### Dafny: A Verification-Oriented Programming Language

Dafny is a language designed around program verification.

```dafny
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  var low := 0;
  var high := a.Length;

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> a[i] > key
  {
    var mid := (low + high) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      return mid;
    }
  }

  return -1;
}
```

Here the verification conditions are written alongside the implementation.

### SPARK: A Verifiable Subset of Ada

SPARK is a verifiable subset of Ada with contract-based specification. It is
widely used in high-assurance domains, especially aerospace.

```ada
procedure Increment (X : in out Integer)
  with Pre  => X < Integer'Last,
       Post => X = X'Old + 1;

procedure Increment (X : in out Integer) is
begin
   X := X + 1;
end Increment;
```

### A Practical Verification Workflow

A realistic workflow usually looks like this:

**1. Requirements analysis and specification**:

```text
informal requirement -> formal specification -> checkable property
```

**2. Staged implementation and proof**:

```text
abstract algorithm -> concrete implementation -> optimization
        |                    |                    |
      proof 1              proof 2              proof 3
```

**3. Integration and whole-system verification**:

```text
component verification -> system integration -> end-to-end verification
```

Program verification is rarely a single theorem. It is an organized pipeline.

### Integration with Automated Tools

Practical verification depends heavily on automation.

**SMT solvers**:

```dafny
lemma ArithmeticProperty(x: int, y: int)
  ensures x + y == y + x
{
}
```

Dafny discharges such obligations automatically with a backend SMT solver such
as Z3.

**Integration with static analysis**:

```c
/*@ requires \valid(ptr);
  @ ensures \result != NULL;
  */
char* safe_malloc_wrapper(size_t size);
```

Combining static analysis with formal contracts often delivers more value than
either technique alone.

### Trade-Offs with Performance and Cost

Practical verification always involves trade-offs between assurance and
efficiency.

**A staged assurance strategy**:

1. fully verify the critical core
2. partially verify important surrounding functions
3. use lighter methods for the rest, such as testing plus static analysis

**A rough cost heuristic**:

```text
verification effort ≈ implementation effort × (2 to 10)
```

The multiplier varies widely with the required assurance level and the
complexity of the artifact.

### Organizational Adoption Strategy

Introducing program verification into an organization requires deliberate
rollout.

**Staged adoption**:

1. **pilot project** to demonstrate value on a small scope
2. **tool and method standardization** to avoid fragmentation
3. **education and training** to build internal capability
4. **continuous improvement** based on feedback

**Success factors**:

- management commitment
- choosing the right problem domain first
- gradual skill building
- collaboration with external experts when needed

### Future Directions

The field continues to evolve in several directions:

- **AI-assisted verification** for tactic suggestion, proof search, and
  candidate generation
- **cloud-based verification** for large-scale distributed proof workloads
- **continuous verification** integrated into CI/CD pipelines

Practical program verification is increasingly a bridge between rigorous theory
and day-to-day engineering.

## 9.7 LLM × Theorem Proving: Automation Layers and Trust Models

Recently, ecosystems such as Lean, Rocq, and Isabelle have increasingly
experimented with LLM-based assistance. The essential trust model remains the
same: even if an LLM generates a candidate proof, the final judgment must come
from the proof assistant's kernel.

This means the right conclusion is not "the AI proved it, so it is correct,"
but rather "the kernel accepted the proof term or script; whether the theorem
statement matches the actual requirement still requires review."

### Where LLM Assistance Is Useful

- searching for tactics or lemmas
- searching libraries
- generating local proof-script candidates
- listing repair candidates from failure logs and goal shapes

Even here, facts and hypotheses should be kept separate, as discussed in
Appendix F.

### Where LLM Assistance Should Not Be Used

- finalizing theorem statements or assumptions without human review
- accepting workflows that silently allow `axiom`, `admit`, or `sorry`

These are high-risk areas because it is easy to prove the wrong statement or
hide an unfinished hole.

### Evaluation Infrastructure

Benchmarks such as ProofGym and APOLLO provide reproducible evaluation
frameworks with fixed datasets and metrics. In operational use, however, a
benchmark score must not be confused with an assurance argument. Acceptance
should still close on the kernel or another authoritative verifier.

### Minimum Review Checklist for AI-Generated Proofs

- does the theorem statement actually match the requirement?
- are prerequisites explicit rather than hidden in imports, axioms, or type
  classes?
- do any unfinished markers remain, such as `admit`, `sorry`, or `axiom`?
- is reproducibility information recorded, including tool version,
  dependencies, and execution steps?

For primary-source guidance, see Appendix E. For a broader checklist, see
Appendix F. For the process of translating natural language into theorem
statements and specifications, see also Chapter 3.6.

## 9.8 The Place of Lean 4: Adoption Decisions and Proof Assets

Lean 4 is a proof assistant based on dependent type theory. It fits naturally
within the Curry-Howard view of "proofs as programs" and is a practical option
for treating proofs as machine-checkable, reusable assets. This book does not
require Lean, but it does provide enough context to evaluate whether adopting
it makes sense.

For environment setup, see the minimal path in Appendix B.

### What Lean 4 Is Good At

- dependent types let teams bring values and specifications closer together and
  preserve boundary conditions or invariants as types
- proof scripts and proof terms can be version-controlled and reviewed
- a small trusted kernel makes the final judgment, while surrounding automation
  remains candidate generation

This aligns well with the trust model discussed for LLM-assisted workflows.

### `term-style` and `tactic-style`: Two Entry Points

Lean 4 supports multiple proof styles for the same theorem.

- **`term-style`** writes the proof directly as an expression and is often a
  good fit for small proofs and direct reuse of library facts
- **`tactic-style`** breaks goals into subgoals interactively and is often
  better suited to larger developments and proof automation

For this book, it is enough to understand these as two operational entry points
into the same proof-engineering discipline.

### A Brief Comparison of Rocq, Isabelle, and Lean

| Viewpoint | Rocq (formerly Coq) | Isabelle/HOL | Lean 4 |
|---|---|---|---|
| Foundation | Type theory (CoC family) | Higher-order logic (HOL) | Dependent type theory |
| Description style | Proof terms + tactics | Structured proof + automation | `term-style` + `tactic-style` |
| Strengths | Integration of proofs and programs, extraction | Strong automation, strong tool integration, strong document workflow | Reuse through `mathlib4`, modern developer experience |
| Good fit | Tight integration of specification and implementation | Large-scale organization of theory, engineering-oriented formalization | Reuse-heavy formalization and continuous maintenance |

All of these systems share one architectural point: the final judgment is made
by a small trusted kernel, while convenience automation lives outside it.

### `mathlib4`: Reusable Proof Assets

In Lean 4, `mathlib4` functions as a de facto standard library. It provides
reusable definitions and theorems across mathematics and computer science.

From a practical perspective, this matters because:

- teams avoid re-proving standard results from scratch
- CI can detect regressions caused by library upgrades
- review can focus more on the theorem statement and dependencies rather than
  on re-deriving common mathematics

### Adoption Checkpoints

Lean 4 should not be viewed as a tool that replaces every other verification
method. It is more realistic to place it in a complementary relationship with
Alloy, TLA+, Dafny, and similar tools.

- **Nature of the property**: is finite exploration enough, or is a general
  theorem needed?
- **Rate of change**: lightweight verification often fits fast-changing code,
  while theorem-proved proof assets fit stable critical cores
- **Operational design**: avoid running every heavy proof on every PR; separate
  workloads by diff, scope, and schedule, as discussed further in Chapter 12

Primary sources:

- Lean official site: <https://lean-lang.org/>
- Lean 4 GitHub: <https://github.com/leanprover/lean4>
- `mathlib4`: <https://github.com/leanprover-community/mathlib4>

---

## End-of-Chapter Exercises

**If you use AI while working through these exercises**

- Treat AI output as a proposal; use verifiers to make the final judgment.
- Keep a record of the prompts you used, the generated specifications and
  invariants, the verification commands and logs (including seed, depth, and
  scope), and the revision history when counterexamples were found.
- For detailed templates, see Appendix D and Appendix F.

### Basic Exercise 1: Formalizing Logical Inference

Formalize the following everyday inferences using natural-deduction rules.

**Inference 1**:
"If it is raining, the ground is wet. It is raining. Therefore the ground is
wet."

**Inference 2**:
"All birds can fly. Penguins are birds. Therefore penguins can fly."
Point out the problem in this inference as well.

**Inference 3**:
"A or B holds. A does not hold. Therefore B holds."

For each inference:

1. formalize the propositions symbolically
2. identify the order of rule application
3. build the proof tree
4. assess whether the inference is valid

### Basic Exercise 2: Basic Proofs in Rocq

Use Rocq to prove the following logical properties:

```coq
Theorem and_commutative : forall P Q : Prop, P /\ Q -> Q /\ P.

Theorem or_commutative : forall P Q : Prop, P \/ Q -> Q \/ P.

Theorem implication_chain : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).

Theorem forall_and_dist : forall (A : Type) (P Q : A -> Prop),
  (forall x, P x /\ Q x) -> (forall x, P x) /\ (forall x, Q x).

Theorem exists_or_dist : forall (A : Type) (P Q : A -> Prop),
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x).
```

### Practical Exercise 1: Proving Data-Structure Properties

Use Rocq to prove the following properties of list operations:

```coq
Fixpoint append (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h :: t => h :: append t l2
  end.

Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => append (reverse t) [h]
  end.

Theorem append_assoc : forall l1 l2 l3 : list nat,
  append (append l1 l2) l3 = append l1 (append l2 l3).

Theorem reverse_append : forall l1 l2 : list nat,
  reverse (append l1 l2) = append (reverse l2) (reverse l1).

Theorem reverse_involutive : forall l : list nat,
  reverse (reverse l) = l.

Fixpoint length (l : list nat) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Theorem length_append : forall l1 l2 : list nat,
  length (append l1 l2) = length l1 + length l2.
```

### Practical Exercise 2: Proving Algorithm Correctness

Use Rocq to prove the correctness of an insertion-sort implementation:

```coq
Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | nil => [x]
  | h :: t => if x <=? h then x :: l else h :: insert x t
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | nil => True
  | [x] => True
  | x :: y :: rest => x <= y /\ sorted (y :: rest)
  end.

Theorem insert_sorted : forall x l,
  sorted l -> sorted (insert x l).

Theorem insertion_sort_sorted : forall l,
  sorted (insertion_sort l).

Inductive Permutation : list nat -> list nat -> Prop :=
| perm_nil : Permutation [] []
| perm_skip : forall x l l', Permutation l l' ->
    Permutation (x::l) (x::l')
| perm_swap : forall x y l,
    Permutation (y::x::l) (x::y::l)
| perm_trans : forall l l' l'',
    Permutation l l' -> Permutation l' l'' ->
    Permutation l l''.

Theorem insertion_sort_permutation : forall l,
  Permutation l (insertion_sort l).
```

### Advanced Exercise: A Practical Verification Project

Choose one of the following practical verification projects.

#### Option 1: A Simple Cryptographic System

```coq
Definition caesar_encrypt (shift : nat) (c : ascii) : ascii :=
  (* Complete the implementation. *).

Definition caesar_decrypt (shift : nat) (c : ascii) : ascii :=
  (* Complete the implementation. *).

Theorem caesar_decrypt_encrypt : forall shift c,
  caesar_decrypt shift (caesar_encrypt shift c) = c.

Theorem caesar_encrypt_decrypt : forall shift c,
  caesar_encrypt shift (caesar_decrypt shift c) = c.
```

#### Option 2: A Balanced Binary Tree

```coq
Inductive tree : Type :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Fixpoint height (t : tree) : nat :=
  (* Compute the height. *).

Definition balanced (t : tree) : Prop :=
  (* Define the balancing condition. *).

Fixpoint insert (x : nat) (t : tree) : tree :=
  (* Implement insertion. *).

Theorem insert_preserves_balance : forall x t,
  balanced t -> balanced (insert x t).

Theorem insert_preserves_bst : forall x t,
  is_bst t -> is_bst (insert x t).
```

#### Option 3: A Concurrent Data Structure

```coq
Definition atomic_compare_and_swap (old new : nat) (location : nat) : bool :=
  (* Abstract the CAS operation. *).

Definition push_spec (x : nat) (pre_state post_state : stack_state) : Prop :=
  (* Preconditions and postconditions of push. *).

Definition pop_spec (pre_state post_state : stack_state)
                    (result : option nat) : Prop :=
  (* Preconditions and postconditions of pop. *).

Theorem push_pop_correctness : forall x s,
  (* Pushing then popping yields the original value. *).

Theorem linearizability : forall operations,
  (* A concurrent execution is equivalent to some sequential one. *).
```

### Evaluation Criteria

Evaluate each exercise from the following perspectives:

1. **Correctness**: the proof is logically complete and valid
2. **Understanding**: the reasoning rules and proof strategy are understood
3. **Efficiency**: the proof is concise and readable
4. **Practicality**: the method can be applied to realistic problems

Through these exercises, the goal is to build both theoretical understanding
and practical ability in theorem proving so that the next chapter on program
verification becomes a natural continuation.
