# Chapter 4: Introduction to Lightweight Formal Methods: Specification with Alloy

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter04.md`

## 4.1 The Philosophy of Alloy: A Lightweight but Powerful Approach

### The Real Meaning of "Lightweight"

The notion of *lightweight* formal methods was popularized by Daniel Jackson at
MIT. The term does not simply mean that the tool is easy to use. It expresses a
fundamentally different stance toward formal methods.

Traditional heavyweight formal methods aimed at complete proof. The goal was to
prove every relevant property mathematically and thereby guarantee correctness
completely. That perfectionist approach had a serious weakness. The learning
cost was high, adoption required a long lead time, and the methods were rarely
used in ordinary projects.

Alloy takes a different path. Its lightweight approach prioritizes practical
value over completeness. Instead of trying to deliver a full proof, it focuses
on discovering counterexamples. Rather than proving that every case is correct,
it tries to find concrete situations in which the design fails, and uses those
findings to improve the design.

### A Heuristic Method Driven by Counterexamples

At the core of Alloy is a counterexample-driven mindset. The idea is close to
scientific hypothesis testing. A scientist cannot usually prove a theory
completely, but can improve the theory by finding evidence that contradicts it.

Software design works similarly. Proving that a design is perfect is difficult,
but finding a concrete example that demonstrates a flaw is often much easier.
Alloy automates that discovery process.

Suppose you are designing an access-control system and want to ensure that only
authorized users can access a file. A traditional approach tries to construct a
mathematical proof. In Alloy, we instead ask whether there exists a situation
in which an unauthorized user can access the file. If such a situation exists,
the design is wrong, and the counterexample gives immediate guidance on how to
repair it.

### Exhaustive Exploration Within a Finite Scope

Another key feature of Alloy is exhaustive exploration within a finite scope.
Real systems have unbounded possibilities, but many important defects can be
discovered through small examples. Alloy therefore explores every possible
instance within a specified bound, such as \"up to three users\" or \"up to five
files.\"

This bound looks like a limitation at first, but in practice it is a major
strength. Inside the chosen scope, the analysis is mathematically rigorous. And
empirically, many design defects do show up in small instances.

For example, when analyzing the possibility of deadlock in a transaction
system, two transactions and two resources are often enough to expose the core
problem. We do not need hundreds of transactions before the design flaw becomes
visible.

### Supporting Exploratory Design

Alloy is not primarily a proof tool. It is an exploration tool. It gives
designers an environment in which they can formulate hypotheses and test them
quickly. That makes iterative improvement at the design stage much more
practical.

In conventional development, design defects are often discovered during
implementation or testing, when the cost of repair is already high. Alloy moves
many of those discoveries forward into the design phase, where changes are
cheaper and the feedback cycle is shorter.

### Background at MIT and Its Lasting Influence

Alloy was developed by the Software Design Group at MIT. Daniel Jackson argued
that many software failures are not implementation problems but conceptual
design problems. According to this view, the decisive mistakes are often made
before any code is written.

That insight shaped Alloy. It is specialized for modeling the essential
structure and behavior of a system without committing to implementation details.
It intentionally stays away from programming-language details, low-level
optimization, and concrete algorithms, and instead focuses on high-level design
questions such as what the system does and which constraints it must satisfy.

### Adoption in Industry and Successful Use Cases

Alloy began as an academic tool, but it is now used in practice as well,
especially for finding specification holes and consistency violations early by
means of bounded checking during design.

What Alloy Analyzer provides is bounded exploration within a given scope. The
guarantee is therefore only that no counterexample exists *within that scope*.
If you want to claim a more general result, you need an additional argument for
why the chosen abstraction and scope are adequate, for example by appealing to
the small-scope hypothesis.

References (primary or official sources):

- Alloy Tools (official): <https://alloytools.org/>
- Daniel Jackson, \"Alloy: A lightweight object modelling notation\" (2002): <https://people.csail.mit.edu/dnj/publications/alloy-journal.pdf>

![Figure 4-1: The overall Alloy approach to lightweight formal methods]({{ '/assets/images/diagrams/alloy-modeling-approach-en.svg' | relative_url }})

## 4.2 Alloy's Worldview: Relational Modeling

### A Paradigm Shift from Objects to Relations

Most programmers are familiar with an object-oriented worldview. We think in
terms of objects, attributes, methods, and messages exchanged among objects.
That worldview is powerful, but it can also limit how we understand system
structure.

Alloy proposes a different worldview: a relational one. A system is described
as a collection of atoms and relations among them. This perspective allows us
to see the structure of the system at a higher level of abstraction and, in
many cases, more directly.

Consider a university enrollment system. In an object-oriented design, we might
create `Student` objects and `Course` objects, and give a student object an
attribute such as an enrollment list. In Alloy, we instead describe the sets
`Student` and `Course` and the relation `enrollment`.

【Tool-compliant (runs as-is)】
```alloy
sig Student {
    enrollment: set Course
}

sig Course {}
```

In this representation, `enrollment` is a field of type `Student -> Course`.
For a student `s`, the expression `s.enrollment` denotes the set of courses
that `s` is enrolled in. Once the relation is explicit, a wide range of
constraints and properties can be described naturally.

### The Structure of the World as Relations

In a relational worldview, everything is understood as a relation. This is
close to the relational model of databases and to graph-theoretic thinking.

- **Ownership relation**: a user owns a file
- **Containment relation**: a folder contains a file
- **Dependency relation**: one module depends on another
- **Inheritance relation**: one class extends another
- **Communication relation**: one process communicates with another

By modeling these relations explicitly, we can analyze the structural
properties of the system in a disciplined way.

### Atoms and Signatures

The most basic building blocks in Alloy are *atoms*. Atoms are indivisible
elements that represent the entities of the system. Atoms are grouped by
*signatures*.

【Pseudo notation】
```text
sig Person {
    age: Int,
    friends: set Person
}

sig Student extends Person {
    courses: set Course
}

sig Teacher extends Person {
    teaches: set Course
}
```

In this example, `Person`, `Student`, and `Teacher` are signatures. The
individual elements that belong to those signatures, such as a concrete student
or a concrete teacher, are atoms.

### Fields as Relational Structure

The fields of a signature are, in fact, relations. `age: Int` is a relation
from `Person` to integers, and `friends: set Person` is a relation from one
`Person` to zero or more other `Person` atoms.

This relational view lets us describe complex structure compactly.

【Pseudo notation】
```text
sig File {
    parent: lone Directory,
    contents: set Byte
}

sig Directory {
    children: set File
}
```

### Facts as Constraints

In Alloy, constraints that must hold in every valid model are written as
*facts*.

【Pseudo notation】
```text
fact NoSelfLoop {
    no p: Person | p in p.friends
}

fact SymmetricFriendship {
    all p1, p2: Person | p1 in p2.friends iff p2 in p1.friends
}

fact FileSystemTree {
    no f: File | f in f.^parent
}
```

### The Expressive Power of Multiplicity

Alloy allows multiplicity constraints to be attached to relations.

- `one`: exactly one
- `lone`: at most one
- `some`: at least one
- `set`: any number, including zero

【Pseudo notation】
```text
sig Car {
    owner: one Person,
    driver: lone Person,
    passengers: set Person
}
```

### Rich Relational Operators

Alloy provides powerful operators over relations.

- **Join**: `r.s`
- **Transpose**: `~r`
- **Transitive closure**: `^r`
- **Reflexive transitive closure**: `*r`

Examples:

【Pseudo notation】
```text
person.^parent

person.follows & person.~follows

directory.*children
```

The first expression denotes all ancestors except the person itself. The second
computes mutual-follow relationships. The third denotes all reachable
descendants including the starting directory.

### Expressing Constraints Relationally

Once the model is centered on relations, even complicated constraints become
natural to write.

【Pseudo notation】
```text
fact AccessControl {
    all f: File, u: User |
        u in f.readers implies (u = f.owner or u in f.authorized)
}

fact DatabaseConsistency {
    all o: Order | o.customer in Customer
    all p: Product | p.stock >= 0
}
```

## 4.3 Describing Basic Structure

### A First Alloy Model: An Address Book

To learn Alloy modeling, let us begin with a familiar example: an address-book
system. Even this small example captures the basic syntax and habits of Alloy.

【Tool-compliant (runs as-is)】
```alloy
module AddressBook

sig Name {}
sig Address {}

sig Contact {
    name: one Name,
    address: lone Address,
    friends: set Contact
}
```

Even this small model already expresses several important points.

- Every contact has exactly one name.
- A contact may have no address at all (`lone` means zero or one).
- A contact may have multiple friends.

### Using Signature Hierarchies

To express more elaborate structure, we can exploit inheritance among
signatures.

【Context-dependent snippet】
```alloy
abstract sig Contact {
    name: one Name,
    address: lone Address,
    friends: set Contact
}

sig PersonalContact extends Contact {
    birthday: lone Date,
    relatives: set PersonalContact
}

sig BusinessContact extends Contact {
    company: one Company,
    position: lone String
}

sig Company {
    employees: set BusinessContact
}
```

The keyword `abstract` means that there are no direct atoms of `Contact`.
Only atoms of the concrete extending signatures exist.

### Refining Structure with Constraints

Bare structure is rarely enough. To make the model realistic, we add facts that
capture consistency requirements.

【Context-dependent snippet】
```alloy
fact ConsistentEmployment {
    all b: BusinessContact, c: Company |
        b in c.employees iff c = b.company
}

fact NoSelfRelation {
    no c: Contact | c in c.friends
    no p: PersonalContact | p in p.relatives
}

fact ReasonableRelatives {
    all p1, p2: PersonalContact |
        p1 in p2.relatives iff p2 in p1.relatives
}
```

### Representing Dynamic Behavior

Alloy can also describe dynamic behavior, not only static structure. One
classic style introduces time explicitly and models change across time points.

【Context-dependent snippet】
```alloy
sig Time {}
open util/ordering[Time]

sig Contact {
    name: one Name,
    address: Address lone -> Time,
    friends: Contact set -> Time
}

pred moveAddress[c: Contact, newAddr: Address, t, tNext: Time] {
    tNext = t.next

    c.address.tNext = newAddr

    all other: Contact - c | other.address.tNext = other.address.t
    all contact: Contact | contact.friends.tNext = contact.friends.t
}
```

This style is still useful to understand because older Alloy models and a large
body of educational material use explicit `Time` or `State` signatures together
with `util/ordering`.

### Practical Example 1: Access Control in an Email System

Let us move to a more realistic example: access control for an email system.

【Tool-compliant (runs as-is)】
```alloy
module EmailSecurity

sig User {
    roles: set Role
}

sig Role {
    permissions: set Permission
}

sig Permission {}

sig Email {
    sender: one User,
    recipients: set User,
    confidential: lone User
}

one sig ReadEmail, SendEmail, AdminAccess extends Permission {}

one sig RegularUser, Manager, Administrator extends Role {}

fact RolePermissions {
    RegularUser.permissions = ReadEmail + SendEmail
    Manager.permissions = ReadEmail + SendEmail
    Administrator.permissions = ReadEmail + SendEmail + AdminAccess
}

pred canReadEmail[u: User, e: Email] {
    u = e.sender or u in e.recipients
    or
    (no e.confidential and ReadEmail in u.roles.permissions)
    or
    (some e.confidential and (u = e.confidential or AdminAccess in u.roles.permissions))
}

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

This example shows how signatures, role-permission assignments, and assertions
combine to form a precise security model.

### Practical Example 2: Inventory Management for an Online Bookstore

The next example includes richer business logic.

【Tool-compliant (runs as-is)】
```alloy
module OnlineBookstore

sig Book {
    isbn: one ISBN,
    price: one Int,
    stock: Int one -> Time
}

sig ISBN {}

sig Customer {
    orders: set Order
}

sig Order {
    items: set OrderItem,
    status: Status one -> Time,
    timestamp: one Time
}

sig OrderItem {
    book: one Book,
    quantity: one Int
}

abstract sig Status {}
one sig Pending, Confirmed, Shipped, Delivered, Cancelled extends Status {}

sig Time {
    next: lone Time
}

fact ValidQuantities {
    all item: OrderItem | item.quantity > 0
    all b: Book, t: Time | b.stock.t >= 0
}

fact OrderIntegrity {
    all o: Order | some o.items
    all item: OrderItem | one item.~items
}

pred reserveStock[b: Book, qty: Int, t, tNext: Time] {
    tNext = t.next
    b.stock.t >= qty
    b.stock.tNext = b.stock.t - qty

    all other: Book - b | other.stock.tNext = other.stock.t
}

pred processOrder[o: Order, t, tNext: Time] {
    tNext = t.next
    o.status.t = Pending

    all item: o.items | item.book.stock.t >= item.quantity

    all item: o.items |
        item.book.stock.tNext = item.book.stock.t - item.quantity

    o.status.tNext = Confirmed
}

assert NoOverselling {
    all b: Book, t: Time |
        b.stock.t >= 0 implies
            (all tPrev: Time | tPrev.^(~next) = t implies b.stock.tPrev >= 0)
}

assert OrderConsistency {
    all o: Order, t: Time |
        o.status.t = Confirmed implies
            (all item: o.items | item.quantity <= item.book.stock.t)
}

check NoOverselling for 5 Book, 5 Order, 10 Time
check OrderConsistency for 5 Book, 5 Order, 10 Time
```

This model is still abstract, but it already captures inventory constraints,
order consistency, and state changes over time.

### Practical Example 3: Leader Election in a Distributed System

As a more advanced example, we can model a leader-election algorithm in a
distributed system.

【Tool-compliant (runs as-is)】
```alloy
module LeaderElection

sig Node {
    id: one Int,
    leader: Node lone -> Time,
    alive: set Time
}

sig Message {
    from: one Node,
    to: one Node,
    content: one MessageType,
    timestamp: one Time
}

abstract sig MessageType {}
one sig Election, OK, Coordinator extends MessageType {}

sig Time {
    next: lone Time
}

fact UniqueIDs {
    all disj n1, n2: Node | n1.id != n2.id
}

fact InitialState {
    some first: Time | no first.~next and
        all n: Node |
            no n.leader.first and
            first in n.alive
}

pred startElection[n: Node, t: Time] {
    t in n.alive
    no n.leader.t

    all higher: Node | higher.id > n.id and t in higher.alive implies
        some m: Message |
            m.from = n and m.to = higher and
            m.content = Election and m.timestamp = t
}

pred respondToElection[receiver: Node, sender: Node, t: Time] {
    t in receiver.alive
    receiver.id > sender.id

    some m: Message |
        m.from = receiver and m.to = sender and
        m.content = OK and m.timestamp = t

    startElection[receiver, t]
}

pred becomeLeader[n: Node, t, tNext: Time] {
    tNext = t.next
    t in n.alive

    no m: Message |
        m.to = n and m.content = OK and m.timestamp = t

    n.leader.tNext = n

    all lower: Node | lower.id < n.id and t in lower.alive implies
        some m: Message |
            m.from = n and m.to = lower and
            m.content = Coordinator and m.timestamp = tNext
}

assert LeaderUniqueness {
    all t: Time | lone n: Node | n.leader.t = n
}

assert LeaderIsAlive {
    all n: Node, t: Time |
        n.leader.t = n implies t in n.alive
}

assert HighestIdWins {
    all t: Time, n: Node |
        n.leader.t = n implies
            (no higher: Node | higher.id > n.id and t in higher.alive)
}

check LeaderUniqueness for 5 Node, 10 Message, 8 Time
check LeaderIsAlive for 5 Node, 10 Message, 8 Time
check HighestIdWins for 5 Node, 10 Message, 8 Time
```

For a self-contained executable example, see `examples/ch04/leader-election.als`.

These practical examples connect directly to later chapters, especially Chapter
8 on model checking and Chapter 11 on integrating formal methods into the
development process.

### Relationships Across Multiple Signatures

Real systems contain multiple kinds of entities connected in nontrivial ways.

【Tool-compliant (runs as-is)】
```alloy
sig User {
    owns: set File,
    groups: set Group
}

sig Group {
    members: set User,
    permissions: set Permission
}

sig File {
    owner: lone User,
    readers: set User,
    groups: set Group
}

sig Permission {}

fact Consistency {
    all u: User, f: File | f in u.owns iff u = f.owner

    all u: User, g: Group | u in g.members iff g in u.groups
}

fact AccessControl {
    all f: File, u: User |
        u in f.readers implies (
            u = f.owner or
            some g: u.groups & f.groups | some g.permissions
        )
}
```

### Defining Utility Predicates

As models grow, reusable predicates improve readability and reduce duplication.

【Context-dependent snippet】
```alloy
pred canAccess[u: User, f: File] {
    u in f.readers or
    u = f.owner or
    some g: u.groups & f.groups | some g.permissions
}

pred orphaned[f: File] {
    no f.owner
}

pred securityViolation {
    some f: File, u: User |
        not canAccess[u, f] and u in f.readers
}
```

### Building a Model Incrementally

Large models should be built in stages.

**Stage 1**: basic entities and relations

【Tool-compliant (runs as-is)】
```alloy
sig File {}

sig User {
    owns: set File
}
```

**Stage 2**: add constraints

【Tool-compliant (runs as-is)】
```alloy
sig File {}

sig User {
    owns: set File
}

fact UniqueOwner {
    all f: File | one u: User | f in u.owns
}
```

**Stage 3**: introduce richer relations

【Tool-compliant (runs as-is)】
```alloy
sig File {}

sig Group {
    groupFiles: set File
}

sig User {
    owns: set File,
    groups: set Group
}
```

**Stage 4**: refine policy and consistency requirements

【Pseudo notation】
```alloy
fact AccessPolicy { ... }
fact ConsistencyRules { ... }
```

Because the final stage contains ellipsis, it is explanatory pseudo notation
rather than code that can be pasted directly into the tool.

## 4.4 Expressing Constraints and Properties

### Constraints as Logical Formulas

One of Alloy's main strengths is that complex constraints can be described as
logical formulas. Requirements that would remain ambiguous in natural language
can be expressed precisely.

The basic logical operators are:

- `and` or `&&`: conjunction
- `or` or `||`: disjunction
- `not` or `!`: negation
- `implies` or `=>`: implication
- `iff` or `<=>`: equivalence

Example: constraints for a university enrollment system.

【Context-dependent snippet】
```alloy
fact EnrollmentRules {
    all s: Student | #s.courses <= 5

    all s: Student | RequiredCourse in s.courses

    all s: Student, c: AdvancedCourse |
        c in s.courses implies c.prerequisite in s.courses
}
```

For a self-contained model, see `examples/ch04/university-enrollment.als`.

### General Constraints with Quantifiers

Quantifiers express notions such as \"for all\" and \"there exists.\"

- `all x: Set | formula`
- `some x: Set | formula`
- `no x: Set | formula`
- `one x: Set | formula`
- `lone x: Set | formula`

Example: constraints for a file system.

【Context-dependent snippet】
```alloy
fact FileSystemInvariants {
    all f: File | lone f.parent

    one d: Directory | no d.parent

    all d: Directory | d not in d.^parent

    some d: Directory | some d.children
}
```

### Expressing Relations with Set Operators

Alloy also relies heavily on set operators.

- `s1 + s2`: union
- `s1 & s2`: intersection
- `s1 - s2`: difference
- `s in t`: subset relation
- `#s`: cardinality

Banking example:

【Tool-compliant (runs as-is)】
```alloy
sig Account {
    owner: one Customer,
    balance: one Int,
    authorized: set Customer
}

sig Customer {
    accounts: set Account
}

sig JointAccount in Account {}

fact BankingRules {
    all a: Account | a.owner in a.authorized

    all a: Account | a.balance >= 0

    all c: Customer, a: Account |
        a in c.accounts iff c = a.owner

    all a: Account | #a.authorized > 1 implies a in JointAccount
}
```

### Expressing Temporal Properties

Alloy can also express dynamic behavior and time-dependent requirements.

【Tool-compliant (runs as-is)】
```alloy
sig State {
    next: lone State,
    users: set User,
    sessions: set Session
}

sig User {}

sig Session {
    user: one User,
    startTime: one State,
    endTime: lone State
}

fact SessionLifecycle {
    all s: Session |
        some s.endTime implies s.endTime in s.startTime.^next

    all s: Session, st: State |
        st in s.startTime.*next and
        (no s.endTime or st in s.endTime.^~next) implies
        s.user in st.users

    all u: User, st: State |
        lone s: Session | s.user = u and
        st in s.startTime.*next and
        (no s.endTime or st in s.endTime.^~next)
}
```

### Formalizing Security Policies

Alloy is particularly well suited to the description of security policies.

【Tool-compliant (runs as-is)】
```alloy
sig Subject {
    roles: set Role,
    clearance: one SecurityLevel
}

sig Object {
    classification: one SecurityLevel,
    owner: one Subject
}

sig Role {
    permissions: set Permission
}

sig Permission {}
sig SecurityLevel {
    dominates: set SecurityLevel
}

one sig ReadPermission, WritePermission extends Permission {}

fact BellLaPadulaModel {
    all s: Subject, o: Object |
        canRead[s, o] implies o.classification in s.clearance.*dominates

    all s: Subject, o: Object |
        canWrite[s, o] implies s.clearance in o.classification.*dominates
}

pred canRead[s: Subject, o: Object] {
    ReadPermission in s.roles.permissions or s = o.owner
}

pred canWrite[s: Subject, o: Object] {
    WritePermission in s.roles.permissions or s = o.owner
}
```

### Layering Invariants

In a complex system, constraints should be organized in layers.

【Context-dependent snippet】
```alloy
fact BasicConsistency {
    all ref: Reference | ref.target in ValidTargets

    all disj x, y: Entity | x.id != y.id
}

fact BusinessRules {
    all p: Product | p.stock >= p.reserved

    all o: Order | o.total = sum[o.items.price]
}

fact SecurityPolicies {
    all s: Subject, r: Resource |
        accesses[s, r] implies authorized[s, r]

    all action: Action | some log: AuditLog | log.action = action
}

fact PerformanceConstraints {
    #CacheEntries <= MaxCacheSize

    #ActiveConnections <= MaxConnections
}
```

This layering clarifies the purpose and criticality of the constraints and
supports staged verification.

## 4.5 Practical Verification with Alloy Analyzer

### The Basic Idea of Model Checking

Alloy Analyzer is the tool that actually explores the model. It applies model
checking within the chosen scope, searching all possible instances in that
bounded space and reporting constraint violations or unexpected behavior.

The basic workflow is:

1. **Generate instances**: produce structures that satisfy the facts.
2. **Check properties**: test whether a target property holds.
3. **Find counterexamples**: if the property fails, produce a concrete failing
   instance.
4. **Analyze results**: use the result to improve the model.

### First Check: Generating Instances

The first step is often to confirm that the model has meaningful instances.
Using the address-book example:

【Context-dependent snippet】
```alloy
run {} for 3

run {
    some c: Contact | #c.friends > 0
} for 3 Contact, 2 Name

run {
    some disj c1, c2: Contact |
        c1 in c2.friends and c2 in c1.friends
} for 4
```

The command `run` checks whether an instance satisfying the constraints exists.
The scope `for 3` means that the exploration may use at most three atoms of
the relevant signatures.

### Assertions: Checking Properties

The keyword `assert` lets us state properties that the model is expected to
satisfy.

【Context-dependent snippet】
```alloy
assert FriendshipSymmetry {
    all c1, c2: Contact |
        c1 in c2.friends implies c2 in c1.friends
}

check FriendshipSymmetry for 5

assert NoOrphanedFiles {
    all f: File | some u: User | f in u.owns
}

check NoOrphanedFiles for 4 User, 6 File
```

The command `check` looks for a counterexample to the assertion. If one is
found, the analyzer shows a concrete instance.

### Interpreting and Using Counterexamples

Consider the following model:

【Tool-compliant (runs as-is)】
```alloy
sig User {
    files: set File,
    groups: set Group
}

sig Group {
    members: set User,
    sharedFiles: set File
}

sig File {}

fact {
    all u: User, g: u.groups | g.sharedFiles in u.files
}

assert NoFileSharing {
    all f: File | lone u: User | f in u.files
}

check NoFileSharing for 3
```

The assertion `NoFileSharing` fails. A counterexample may look as follows.

【Pseudo notation】
```text
User0: files = {File0}, groups = {Group0}
User1: files = {File0}, groups = {Group0}
Group0: members = {User0, User1}, sharedFiles = {File0}
File0: (file)
```

This counterexample makes the design contradiction explicit: the model of group
sharing allows multiple users to hold the same file, which conflicts with the
assertion.

### Choosing Scopes Effectively

The chosen scope has a major effect on both performance and usefulness.

【Context-dependent snippet】
```alloy
check BasicProperty for 2

check ScalabilityProperty for 2 User, 6 File, 3 Group

check ComplexProperty for 8

check ConditionalProperty for 4 but exactly 2 Admin
```

General guidelines:

- Start with a small scope, such as two or three elements, to find basic
  problems quickly.
- If no issue is found, increase the scope gradually.
- If one kind of element is especially important, control that scope
  separately.

### Staged Verification with Predicates

Complex scenarios can be explored in stages by using predicates.

【Context-dependent snippet】
```alloy
pred initialState {
    no User.files
    no Group.sharedFiles
}

pred createFile[u: one User, f: one File] {
    f not in u.files
    no other: User - u | f in other.files
}

pred securityBreach {
    some u: User, f: File |
        f in u.files and
        not authorized[u, f]
}

run initialState for 3
run { initialState and some u: User, f: File | createFile[u, f] } for 3
check { not securityBreach } for 4
```

### The Iterative Model-Improvement Process

Practical use of Alloy usually follows an iterative cycle.

**1. Build the initial model**

【Tool-compliant (runs as-is)】
```alloy
sig Document {
    owner: one User,
    readers: set User,
    authorized: set User
}

sig User {}

fact BasicSecurity {
    all d: Document | d.owner in d.readers
}
```

**2. Perform a first verification**

【Context-dependent snippet】
```alloy
run {} for 3
assert OwnerCanRead { all d: Document | d.owner in d.readers }
check OwnerCanRead for 3
```

**3. Discover a problem and refine requirements**

【Context-dependent snippet】
```alloy
pred collaborativeDocument {
    some d: Document | #d.readers > 1
}

run collaborativeDocument for 3
```

**4. Add a new constraint**

【Context-dependent snippet】
```alloy
fact SharePolicy {
    all d: Document, u: User |
        u in d.readers and u != d.owner implies
        u in d.authorized
}
```

**5. Verify again**

【Context-dependent snippet】
```alloy
assert NoUnauthorizedAccess {
    all d: Document, u: User |
        u in d.readers implies
        (u = d.owner or u in d.authorized)
}

check NoUnauthorizedAccess for 4
```

By repeating this cycle, the model can be improved incrementally instead of
being treated as fixed from the beginning.

## 4.6 Alloy 6 Extensions: Mutable State and Temporal Logic

Historically, Alloy was strongest for checking the consistency of static
structure expressed as relations. In **Alloy 6**, however, the introduction of
`var` and temporal operators makes it possible to describe state transitions and
traces directly. This reduces the need for the classic `State`-signature plus
`ordering` encoding that was common in Alloy 4.

The execution environment used in this book, described in Appendix B, fixes
Alloy `6.2.0` through `tools/bootstrap.sh`. The same commands should therefore
be reproducible for readers unless they intentionally override
`ALLOY_VERSION`.

### Basic Syntax in Alloy 6

- `var`: declare a signature or field whose value changes across states
- `'` (prime): refer to the value in the next state, as in `Trash' = Trash + f`
- temporal operators such as `always`, `eventually`, `once`, and `after`
- `n steps`: bound the trace length; larger scope and more steps mean higher
  exploration cost

### Example: The Trash Model

`examples/alloy/trash-temporal.als` is a minimal model with a set `File` and a
mutable subset `Trash`. Delete and restore operations are described as
transitions, and a simple safety property is checked.

【Tool-compliant (runs as-is)】
```alloy
sig File {}

var sig Trash in File {}

pred delete[f: File] {
  f not in Trash
  Trash' = Trash + f
}

pred restore[f: File] {
  f in Trash
  Trash' = Trash - f
}

pred stutter {
  Trash' = Trash
}

fact init {
  no Trash
}

fact transitions {
  always (stutter or some f: File | delete[f] or restore[f])
}

example: run { eventually (some Trash and after no Trash) } for 3 but 6 steps

assert restoreAfterDelete {
  always (all f: File | restore[f] implies once delete[f])
}
check restoreAfterDelete for 3 but 6 steps
```

Command-line execution:

【Tool-compliant (runs as-is)】
```bash
bash tools/bootstrap.sh
bash tools/alloy-check.sh --verbose examples/alloy/trash-temporal.als
```

How to read the results:

- `run` checks for the existence of a trace. `SAT` means that a trace
  satisfying the condition exists.
- `check` looks for a counterexample. `UNSAT` means that no counterexample was
  found within the given scope and step bound. It does **not** mean that a
  general proof has been established outside those bounds.

Generated artifacts:

- The trace is written to `.artifacts/alloy/trash-temporal/example-solution-0.md`.
- To visualize it in the GUI, run `java -jar tools/.cache/alloy-6.2.0.jar gui`
  and step through the states interactively.

## 4.7 Learning from Counterexamples: The Design Improvement Cycle

### The Educational Value of Counterexamples

The counterexamples produced by Alloy Analyzer are more than error messages.
They are concrete learning material. A counterexample shows not only that a
problem exists, but also how the design decisions made that problem possible.

Strong designers do not stop at \"there is a bug.\" They ask deeper questions:
Why is this situation possible? Is it truly unacceptable? Is the root cause a
missing constraint, a vague requirement, or a flawed design concept?

### Example: Improving an Access-Control System

Let us trace an improvement cycle for a file access-control system.

**Initial design**:

【Tool-compliant (runs as-is)】
```alloy
sig User {
    owns: set File,
    canRead: set File
}

sig File {
    owner: one User
}

fact OwnershipConsistent {
    all f: File | f in f.owner.owns
    all u: User, f: u.owns | f.owner = u
}

fact OwnerCanRead {
    all u: User | u.owns in u.canRead
}

assert SecureAccess {
    all u: User | u.canRead = u.owns
}

check SecureAccess for 3
```

**Counterexample**:

【Pseudo notation】
```text
User0: owns = {File0}, canRead = {File0, File1}
User1: owns = {File1}, canRead = {File1}
File0: owner = User0
File1: owner = User1
```

The counterexample shows that `User0` can read `File1`. That may be contrary
to the designer's intent, but under the current facts it is legal.

**Design review prompted by the counterexample**:

1. Should file sharing be allowed at all?
2. If it is allowed, what control mechanism is required?
3. How should read permission for non-owners be represented?

**Improved design**:

【Tool-compliant (runs as-is)】
```alloy
sig User {
    owns: set File
}

sig File {
    owner: one User,
    sharedWith: set User
}

fun canRead: User -> File {
    owns + ~sharedWith
}

fact SharePolicy {
    all f: File | f.sharedWith in User - f.owner
}

assert AuthorizedAccessOnly {
    all u: User, f: File |
        f in canRead[u] iff (f in u.owns or u in f.sharedWith)
}

check AuthorizedAccessOnly for 4
```

### Extending the Design to Group-Based Access Control

Even this simple sharing model may reveal further counterexamples.

【Context-dependent snippet】
```alloy
pred LargeSharedFile {
    some f: File | #f.sharedWith > 2
}

run LargeSharedFile for 5
```

This exploration shows that a single file may be shared with many users. That
may or may not be acceptable, depending on the requirements. If it becomes a
management problem, a group-based model may be more appropriate.

**Improved group-based model**:

【Tool-compliant (runs as-is)】
```alloy
sig User {
    owns: set File,
    memberOf: set Group
}

sig Group {
    members: set User,
    files: set File
}

sig File {
    owner: one User,
    groups: set Group
}

fact GroupConsistency {
    all u: User, g: Group |
        u in g.members iff g in u.memberOf

    all f: File, g: Group |
        f in g.files iff g in f.groups
}

fun canAccess: User -> File {
    owns + (memberOf.files)
}

assert GroupAccessControl {
    all u: User, f: File |
        f in u.canAccess iff
        (f in u.owns or some g: u.memberOf | f in g.files)
}

check GroupAccessControl for 4
```

### Finding and Addressing Temporal Constraints

Counterexamples can also reveal temporal design problems.

【Tool-compliant (runs as-is)】
```alloy
open util/ordering[Time]

sig Time {}

sig User {
    active: set Time
}

sig Session {
    user: one User,
    start: one Time,
    end: lone Time
}

fact SessionLifetime {
    all s: Session |
        some s.end implies s.end in s.start.^next
}

pred ConcurrentSessions {
    some disj s1, s2: Session |
        s1.user = s2.user and
        some t: Time |
            t in s1.start.*next and t in s2.start.*next and
            (no s1.end or t in s1.end.^~next) and
            (no s2.end or t in s2.end.^~next)
}

run ConcurrentSessions for 3 User, 4 Session, 5 Time
```

This exploration reveals the possibility of concurrent sessions for the same
user. Whether that is acceptable depends on the intended policy.

### Predicting Performance Problems

Alloy can also help predict performance risks.

【Tool-compliant (runs as-is)】
```alloy
sig Database {
    tables: set Table,
    connections: set Connection
}

sig Table {
    rows: set Row,
    indexes: set Index
}

sig Row {}
sig Index {}

sig Connection {
    queries: set Query
}

sig Query {
    targetTable: one Table,
    filterConditions: set Condition
}

sig Condition {}

fact PerformanceConstraints {
    all t: Table | #t.rows > 100 implies some t.indexes

    all d: Database | #d.connections <= 50
}

pred PerformanceBottleneck {
    some q: Query |
        #q.targetTable.rows > 1000 and
        no q.targetTable.indexes and
        #q.filterConditions > 0
}

run PerformanceBottleneck for 3
```

This model does not measure runtime directly, but it does expose structures
that are likely to produce poor performance.

### A Methodology for Counterexample-Driven Design Improvement

To use counterexamples effectively, a systematic process is helpful.

1. **Classify the counterexample**
   - a genuine design defect
   - an ambiguity in the requirements
   - an incompleteness in the model
   - an unexpected but acceptable situation
2. **Analyze the root cause**
   - Why does the situation arise?
   - Which constraint is missing?
   - Which assumption was left implicit?
3. **Choose a response strategy**
   - add a constraint
   - restructure the model
   - clarify the requirement
   - accept the behavior if it is not actually problematic
4. **Verify the improvement**
   - confirm the effect of the new constraint
   - evaluate its impact on other properties
   - rerun the analysis at a larger scope if needed

With this disciplined approach, counterexamples become one of the most
effective tools for improving a design.

---

## End-of-Chapter Exercises

**If you use AI while working through these exercises**

- Treat AI output as a proposal; use verifiers to make the final judgment.
- Keep a record of the prompts you used, the generated specifications and
  invariants, the verification commands and logs (including seed, depth, and
  scope), and the revision history when counterexamples were found.
- For detailed templates, see Appendix D and Appendix F.

### Basic Exercise 1: Reading an Alloy Model

Read the following Alloy model and explain the system structure and constraints
that it represents.

【Tool-compliant (runs as-is)】
```alloy
sig Person {
    spouse: lone Person,
    parents: set Person,
    children: set Person
}

fact FamilyRules {
    all p1, p2: Person | p1.spouse = p2 iff p2.spouse = p1

    all p1, p2: Person | p1 in p2.parents iff p2 in p1.children

    all p: Person | p not in p.parents

    all p: Person | no p.spouse & p.parents
}
```

Explain:

1. The real-world concepts represented by the signatures
2. The meaning and plausibility of each constraint
3. Whether there are family relationships that the model cannot represent
4. Plausible counterexamples and what they would mean

### Basic Exercise 2: Writing Constraints

For an online library system, write Alloy constraints satisfying the following
requirements.

**Requirements**:

- A user may borrow multiple books.
- A book may not be lent to multiple people at the same time.
- A user may borrow at most five books.
- A user with overdue items may not borrow new books.
- Every book has a due date.

Define the necessary signatures and facts.

### Practical Exercise 1: Modeling a Security Policy

Model a file access-control system in Alloy that satisfies the following
requirements.

**Functional requirements**:

- Users can own files.
- Files are either read-only or read-write.
- Groups can be created and users can be added to them.
- Files can be shared with groups.

**Security requirements**:

- The owner can always access the file.
- Group members can access only files shared with that group.
- Writing to a read-only file is forbidden.
- Administrators can access all files.

Tasks:

1. Define appropriate signatures.
2. Write facts for the constraints.
3. Write assertions for the security properties.
4. Verify them using `check`.

### Practical Exercise 2: Model Checking and Improvement

For the model created in the previous exercise:

1. Try various `run` commands to generate instances.
2. Execute checks under different scopes.
3. Analyze any counterexamples that are found.
4. Improve the constraints or the design.
5. Verify the improved version again.

### Advanced Exercise: Modeling Dynamic Behavior

Using Alloy 6 `var` declarations and temporal operators, model the dynamic
behavior of the following ATM system, referring to Section 4.6.

**ATM system**:

- Accounts have balances.
- A withdrawal decreases the balance.
- A deposit increases the balance.
- A withdrawal is forbidden if funds are insufficient.
- Every transaction is recorded in the history.

Tasks:

1. Declare state such as account balances and transaction history using `var`.
2. Define each operation as a current-state to next-state predicate using
   expressions such as `x' = ...`.
3. Write invariants and forbidden conditions with `always`, and search for
   counterexamples with `check`.
4. Adjust both the exploration scope and the trace length with `for ... but ...
   steps`, then iterate through counterexample, repair, and re-verification.

Supplement: a classic Alloy 4 style based on an explicit `State` signature and
`util/ordering` can still be used, but this book treats the Alloy 6 notation
as the primary style.

**Properties to verify**:

- Balances remain non-negative.
- The total amount of money is preserved before and after each transaction.
- Every transaction is recorded in the history.

By working through these exercises, you should develop practical skill in
Alloy-based modeling and be prepared for the more advanced formal methods
presented in the next chapter.
