# Chapter 1: Why Formal Methods Matter

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter01.md`

## 1.1 The Growth of Software Complexity and the Challenge of Reliability

From the moment you stopped your smartphone alarm this morning to the moment
you started reading this page, how many software systems have you interacted
with? An alarm app, weather forecasting, email, transportation information,
payment services, security authentication, and countless background processes.
Daily life now rests on a vast foundation of software systems operating out of
sight.

The complexity of that invisible foundation has grown exponentially over the
past thirty years. A typical application in the 1990s ran on a single machine
and consisted of, at most, tens of thousands of lines of code. Modern systems
are different. When you submit one search query in a web browser, hundreds of
servers across the world may coordinate in a fraction of a second, millions of
lines of code may execute, multiple databases may be updated, security checks
may run, and recommendation algorithms may be invoked.

This complexity is not additive. As the number of system components increases,
the interactions among them grow combinatorially. Mathematically, the number of
possible pairwise interactions among `n` components is
`C(n,2) = n(n-1)/2`. With ten components there are 45 possible interactions.
With 100 components there are 4,950. With 1,000 components there are roughly
half a million. Modern software systems often contain tens of thousands or even
hundreds of thousands of relevant elements, so the interaction space becomes
astronomical.

This explosion of complexity is a foundational challenge in software
engineering. Formal methods provide a mathematical approach to combinatorial
explosion and a way to reason systematically about spaces of behavior that
otherwise look unbounded.

### The Nature of Complexity: Unexpected Behavior Emerges

What this combinatorial complexity produces is often called *emergent
behavior*. Individual components may work correctly in isolation, yet their
combination may produce behavior nobody anticipated.

The 2003 Northeast blackout in North America began with a software failure in a
control system used by an Ohio power company. The triggering fault was small.
Its consequences were not. The disturbance propagated through interacting power
systems and eventually affected about 50 million people. Each subsystem had
been designed for normal operation, but their interaction produced an outcome
that the designers had not adequately predicted.

This phenomenon is especially visible in software systems. Software is
inherently discrete, so a very small change can produce a radically different
overall result. In many physical systems, small errors tend to produce small
effects. In software, a one-bit difference can completely change the behavior
of an entire system.

### The Mathematical Nature of Emergent Complexity

In systems theory, emergent behavior is often described in terms of nonlinear
interaction. The overall behavior `F(S)` of the system cannot be reduced to the
simple sum `Σf(si)` of the behaviors of its individual components:

Pseudo notation:

```text
F(S) ≠ Σf(si)
```

This nonlinearity is exactly the territory where formal methods become most
valuable. Chapter 8 introduces model checking as a technique for systematically
enumerating interactions and exploring a system's state space. Chapter 9 then
introduces theorem proving as a way to obtain mathematical guarantees even in
the presence of complex interaction.

### Rising Social Demands for Reliability

At the same time, society has become far more dependent on software and far
less tolerant of its failure. If a banking system stops for an hour, the loss
may amount to hundreds of millions of yen. A software defect in a medical
device can directly threaten human life. In self-driving vehicles and aircraft
control systems, software reliability affects passenger safety directly.

This increased social dependence places software developers under a level of
responsibility that earlier generations rarely faced. In the past, many teams
could dismiss bugs as unfortunate but inevitable. Today, failures often carry
legal and social consequences. Regulatory pressure has also intensified through
frameworks such as the GDPR in Europe, medical-device regulation in the United
States, and standards such as DO-178C in aerospace.

### Safety Integrity Levels and Where Formal Methods Apply

Safety-critical systems are often classified by criticality, but different
standards use different schemes. IEC 61508 uses Safety Integrity Levels
(SILs), while ISO 26262 uses Automotive Safety Integrity Levels (ASILs) for
road vehicles. A generic SIL-oriented classification looks like this:

- **SIL 4 (highest level)**: aircraft flight control and nuclear control
  systems
- **SIL 3**: railway signaling and life-support functions in medical devices
- **SIL 2**: industrial safety interlocks and process-protection systems
- **SIL 1**: alarm and monitoring systems

For higher-assurance categories such as SIL 3 and SIL 4, and for the higher
ASIL categories in automotive systems, the use of formal methods is strongly
recommended and, in many contexts, effectively becomes a regulatory
expectation. Chapter 11 examines the relationship between such safety
standards and formal methods in more detail.

### The Fundamental Dilemma Between Complexity and Reliability

This leaves us with a fundamental dilemma. We want software systems that are
more capable and more sophisticated. At the same time, we demand higher
reliability from those systems. Under conventional approaches, however,
complexity and reliability are difficult to improve together.

Adding features increases complexity and therefore increases the number of ways
the system can fail. Improving reliability through testing and review increases
cost and often slows delivery. Resolving that tension requires an approach that
is fundamentally different from ordinary empirical quality control.

Formal methods provide one answer to that dilemma. They offer a path for
reasoning rigorously about complex systems and for obtaining stronger
assurance. But why mathematics? To answer that, it helps to begin with history.

![Figure 1-1: Exponential growth in software complexity and rising reliability demands]({{ '/assets/images/diagrams/software-complexity-evolution.svg' | relative_url }})

## 1.2 Learning from History: Major Failures and Their Lessons

### The Ariane 5 Disaster: Ambiguous Specifications as a Cause of Catastrophe

On June 4, 1996, the first Ariane 5 launch vehicle built by the European Space
Agency exploded 37 seconds after liftoff. It carried four expensive scientific
satellites, and the financial loss was enormous. More important than the cost,
however, was the loss of confidence in Europe's space program and the waste of
more than a decade of engineering effort.

The immediate cause was a simple software error. The inertial reference system
attempted to convert a 64-bit floating-point value into a 16-bit signed
integer, and the conversion overflowed. The code responsible had been reused
from Ariane 4, where it had never caused trouble. Why did it fail on Ariane 5?

The answer lay in ambiguity in the specification. The documented assumptions
about the range of the variable representing horizontal velocity were not
sufficiently precise. Under Ariane 4 flight conditions, the value stayed within
the 16-bit range. Ariane 5 had more powerful engines and followed a different
trajectory. As a result, the same variable took on a larger value, and the
overflow occurred.

Several lessons follow from this failure. First, the fact that software has
worked before does not imply that it is correct. Ariane 4 demonstrated success
under particular conditions; it did not prove correctness for changed
conditions.

Second, ambiguous specifications can be fatal. The phrase "horizontal velocity"
looks clear enough to a human reader, but the allowable range of values, the
required precision, and the behavior in exceptional situations had not been
captured rigorously. That ambiguity enabled an unexpected failure mode.

### Therac-25: The Absence of Formal Specification in a Medical Setting

An even more serious case is the Therac-25 radiation-therapy accident, which
occurred between 1985 and 1987. Because of software errors in the treatment
machine, six patients received massive overdoses of radiation, and at least
three died.

The root problem was not merely a local programming defect. The deeper problem
was that the safety specification for the system was incomplete. The designers
tried to implement in software the safety protections that had previously been
enforced by hardware in the earlier Therac-20 generation. Yet the software
specification for safe control had never been subjected to formal verification.

The immediate cause of the accidents was a race condition. If an operator
entered keys in a certain sequence, the software could reach an inconsistent
state and enable a treatment electron beam at far greater intensity than what
was intended for diagnostic X-ray mode. The problem was difficult to reproduce,
and early incident reports were initially dismissed as vague malfunctions.

The lesson here is clear: in safety-critical systems, intuition and experience
are not enough to guarantee safety. Once concurrency and asynchrony enter the
picture, the combination of reachable states can exceed unaided human
reasoning. Formal specification becomes a practical necessity, not an academic
luxury.

### Continuity into the Present: The Problem Has Not Gone Away

These incidents are not relics of an earlier era. The Boeing 737 MAX crashes,
which became publicly central in 2018 and 2019, were modern expressions of the
same pattern. The Maneuvering Characteristics Augmentation System (MCAS) acted
on the basis of a single faulty sensor input and overrode pilot control.

Here again, ambiguity in system behavior was central. The operating conditions
for MCAS, the duration of its intervention, and its interaction with pilot
actions were not specified with sufficient rigor. As a result, pilots faced
system behavior they were not adequately prepared to interpret or counteract.

The same structural pattern appears in more recent incidents as well: the Tokyo
Stock Exchange outage on October 1, 2020, the Boeing 737 MAX software failures,
and the 2017 Equifax data breach all reflect, at a deeper level, ambiguity in
complex system behavior and the emergence of unexpected interactions
([JPX statement](https://www.jpx.co.jp/corporate/news/news-releases/0060/20201019-01.html),
[FSA statement](https://www.fsa.go.jp/news/r2/shouken/20201130-1.html)).

### Common Patterns Revealed by Accident Analysis

When we examine these incidents closely, several recurring patterns appear:

- **Ambiguous specifications**: system behavior is described in natural
  language, leaving room for incompatible interpretations.
- **Implicit assumptions**: prerequisites based on experience or intuition are
  never made explicit in the design documents.
- **The trap of local optimization**: each component works in isolation, yet
  the full system exhibits unexpected interaction.
- **Incomplete verification**: testing and review miss failures that occur only
  under rare combinations of conditions.

These patterns reveal structural limits in conventional software development
practice. Overcoming those limits is one of the core reasons formal methods are
needed.

## 1.3 The Limits of Conventional Methods

### What Test-Driven Development Achieves and Where It Stops

Test-driven development (TDD) is one of the most important practices in modern
software engineering. By writing tests before code, teams clarify expected
behavior and often improve quality significantly. TDD has real value and many
demonstrated successes.

Still, TDD has structural limits. The most important is that testing does not
prove correctness. It only checks behavior under the conditions represented by
the chosen tests. As the Ariane 5 case showed, successful behavior in Ariane 4
did not establish correctness for Ariane 5.

In mathematical terms, TDD can provide *existential evidence* but not
*universal proof*. It can show that a specific input produces a desired output.
It cannot establish that every possible input produces a correct result.

### Test Coverage and Combinatorial Explosion

In real software systems, the input space is enormous. A function that accepts
a single 32-bit integer already has roughly 4.3 billion possible inputs. With
multiple arguments, the combinations quickly become astronomical.

For a function with three 32-bit integer arguments, the total number of input
combinations is:

- `(2^32)^3 ≈ 7.9 × 10^28`

That is obviously far beyond exhaustive testing. Chapter 3 introduces
specification techniques for abstracting enormous input spaces mathematically.
Chapter 10 later explains how techniques such as loop invariants make it
possible to reason about unbounded repetition in a finite way.

### The Human Limits of Code Review

Code review improves software quality by using the collective judgment of a
development team. Experienced reviewers can find many important issues. Yet
human cognition is limited.

A commonly cited rule of thumb is that people can actively keep track of only
about seven plus or minus two items at once. Modern software systems, by
contrast, may involve thousands or tens of thousands of variables, functions,
and interacting conditions. No reviewer can hold all of those interactions in
their head simultaneously.

Concurrency and timing-related failures are particularly difficult to uncover
through static reading alone. Therac-25 is again a good example: each fragment
of the code could look reasonable when reviewed locally, yet the dangerous
interaction emerged only in the right operational sequence.

### The Partial Effectiveness of Static Analysis Tools

Modern static analysis has improved greatly. Compilers and analyzers can detect
type errors, uninitialized variables, memory leaks, and many other classes of
defect automatically.

Even so, static analysis has limits. Most importantly, it can often analyze
what a program *does*, but not what a program *should do*. That is, it cannot
reliably detect a gap between the implementation and the intended
specification.

Static analysis must also be conservative. To avoid excessive false positives,
tools may miss subtle defects that arise only under complex semantic
conditions.

### The Complementary Value of Conventional Methods

Pointing out these limitations does not mean discarding conventional methods.
TDD, code review, and static analysis all provide important value. The issue is
that, by themselves, they do not scale to the full complexity of modern
software systems.

An analogy from civil engineering is useful here. Conventional software quality
practices correspond to construction-site quality control: inspecting
materials, relying on skilled workers, and managing the build process. All of
that matters. But for a skyscraper or a long bridge, those practices are not
enough. Structural calculation is also required. In contemporary software
engineering, formal methods play a role similar to structural calculation.

### The Mathematical Meaning of Completeness

At a deeper level, the limitations of conventional methods are limitations of
*completeness*. Testing checks only finitely many cases, not all possible ones.
Review is bounded by human cognition. Static analysis can detect many syntactic
and local issues, but not complete semantic correctness against an intended
meaning.

Formal methods aim to provide that stronger notion of completeness. A
mathematical proof can establish that a system behaves according to its
specification for all admissible inputs or all reachable states within a given
model. That is a categorically stronger guarantee.

Such completeness, however, is not free. Formal methods take time to learn,
take effort to apply, and cannot express every requirement equally well. The
practical goal is therefore not to replace conventional methods, but to
complement them intelligently.

## 1.4 New Horizons Opened by the Mathematical Approach

### Rigor as a New Quality Dimension

The most important value formal methods provide is a new quality dimension:
*rigor*. Traditional software quality is usually discussed in terms of
functionality, performance, maintainability, and availability. Formal methods
add mathematical correctness as a first-class concern.

This rigor has concrete practical value. A mathematically precise
specification reduces ambiguity and minimizes misunderstanding. Different
developers reading the same specification can converge on the same
interpretation. In large teams and long-running projects, that can reduce
communication cost dramatically.

### Verification at the Design Stage as a Paradigm Shift

Under conventional development processes, many problems are found only after
implementation, during testing or operations. Formal methods make it possible
to discover many problems during requirements and design. That is a profound
shift in quality assurance.

The economic value of early detection is substantial. A design correction may
take hours or days. A post-implementation correction may take weeks or months.
A production incident can affect the entire business.

Large cloud providers such as Amazon have used TLA+ to verify distributed
system designs before implementation. That makes it possible to uncover subtle
concurrency flaws early and avoid large-scale failures later.

### The Future Possibility of Automation

Another major value of formal methods lies in automation. Once a specification
is mathematically precise, it becomes possible to generate test cases from it.
In some settings, it is also possible to generate implementation code
automatically from the specification.

This is more than efficiency. If code is generated from a trusted formal
specification, the risk of misreading the requirement or introducing a local
implementation error can be reduced significantly.

Industries such as railway control and aerospace have already used
specification-driven generation in practice. The fully automated operation of
Paris Metro Line 14, for example, is one of the often-cited cases where formal
methods played a major role in the development process.

### Proof as a Reusable Knowledge Asset

Proofs built through formal methods become reusable assets. Once a property has
been proved for a design, later projects can build on that result rather than
re-establishing everything from scratch.

For example, if the correctness of a cryptographic algorithm or protocol is
proved formally, every system that relies on that verified artifact benefits
from the result. This creates a cumulative improvement in quality across the
industry.

### The New Role of Formal Methods in the Age of AI

The spread of artificial intelligence and machine learning makes formal methods
more important, not less. AI behavior is often harder to predict than that of
traditional software. Learning-based systems can change behavior over time, and
small changes in input can lead to large changes in output.

In safety-critical AI systems such as autonomous vehicles, medical diagnosis,
and financial decision support, formal methods are increasingly relevant as a
way to constrain or verify important safety properties. At the same time,
formal methods and AI are beginning to reinforce one another: AI can help with
the construction of specifications, while formal methods can help establish
safety envelopes and consistency guarantees for AI-based systems.

### Responsibility for Software as Social Infrastructure

Software is now part of society's critical infrastructure, much like
electricity or water. That reality imposes a new kind of responsibility on
software engineers. Software is no longer only a vehicle for convenience. It
is a foundation for safety, finance, communication, transportation, and public
trust.

Meeting that responsibility requires more than individual talent or experience.
It requires engineering discipline grounded in mathematics. Formal methods are
an important part of that maturation of software engineering.

### The Journey of This Book: A Step-by-Step Learning Approach

This book is an invitation into the world of formal methods. You will become
comfortable with mathematical notation, develop habits of logical reasoning,
and learn how to design complex systems more rigorously.

The learning path is divided into four stages:

**Part I (Foundations)**: motivation and core concepts
- why formal methods matter (this chapter)
- the natural relationship between programming and mathematics (Chapter 2)
- writing specifications that eliminate ambiguity (Chapter 3)

**Part II (Methods)**: major formal techniques
- lightweight verification with Alloy (Chapter 4)
- state-based specification with Z notation (Chapter 5)
- concurrent systems with CSP (Chapter 6)
- time-aware specification with TLA+ (Chapter 7)

**Part III (Verification)**: checking system correctness
- automatic verification by model checking (Chapter 8)
- rigorous proof by theorem proving (Chapter 9)
- practical program verification (Chapter 10)

**Part IV (Practice)**: applying formal methods in real projects
- integration into development processes (Chapter 11)
- tool ecosystems and automation (Chapter 12)
- real-world case studies (Chapter 13)

At first, these topics may feel abstract. But once you acquire them, you gain
the ability to build software that is more dependable, easier to understand,
and easier to maintain. That is valuable both for individual careers and for
society as a whole.

### Learning Outcomes and Practical Value

By the end of this book, you should be able to develop the following practical
capabilities:

**Technical capabilities**
- writing specifications without ambiguity
- verifying the safety of complex systems mathematically
- analyzing the root causes of defects in a systematic way

**Project and process capabilities**
- building quality-assurance processes that work at the design stage
- identifying high-risk areas before implementation
- forming technical consensus with stakeholders on the basis of precise
  arguments

**Career value**
- qualifying for work on safety-critical systems
- participating more effectively in advanced technical discussions
- understanding the direction of next-generation software engineering

The next chapter takes the first concrete step into this mathematical approach
by examining the natural relationship between programming and mathematics.
Formal methods are not a separate world. They are a disciplined extension of
concepts software engineers already use every day.

![Figure 1-2: A structured roadmap for learning formal methods across four parts and thirteen chapters]({{ '/assets/images/diagrams/formal-methods-roadmap.svg' | relative_url }})

---

## End-of-Chapter Exercises

**If you use AI while working through these exercises**

- Treat AI output as a proposal; use verifiers to make the final judgment.
- Keep the prompts you used, generated specifications and invariants,
  verification commands and logs (including seed, depth, and scope), and the
  revision history when counterexamples were found.
- See Appendix D and Appendix F for detailed templates.

### Thinking Exercise 1: Complexity Analysis

Choose one software system that you use regularly (for example, online banking,
a smartphone map application, or an email system) and analyze it from the
following perspectives:

1. **Identify system components**: list the major elements of the system
   (servers, databases, APIs, UI, and so on) and describe the role of each.
2. **Analyze interaction**: draw the interactions among components and evaluate
   the complexity in terms of combinatorial explosion.
3. **Analyze failure modes**: explain how failure in each component could affect
   the system as a whole, and consider the possibility of emergent behavior.
4. **Assess the safety integrity level**: determine which SIL level the system
   would correspond to and evaluate whether formal methods are justified.

**Suggested scope**: a short memo with one diagram or table. In most cases,
two pages or less is enough.

### Practical Exercise: Accident Analysis and Preventive Measures

Choose one of the cases introduced in this chapter (Ariane 5, Therac-25, or
Boeing 737 MAX) and perform the following analysis:

1. **Technical root-cause analysis**
   - Identify the direct technical cause.
   - Explain how ambiguity in the specification contributed to the problem.
   - Explain how interaction among subsystems produced an unexpected result.

2. **Could formal methods have prevented it?**
   - Could the issue have been exposed with the Alloy modeling introduced in
     Chapter 4?
   - Could the problem have been found with the model-checking techniques in
     Chapter 8?
   - Which properties might have been proved with the program-verification
     techniques in Chapter 10?

3. **Lessons for the present**
   - Could a similar issue arise in current systems?
   - Where do you see analogous risks in your own work?
   - What concrete actions would reduce that risk?

**Suggested scope**: a short slide deck or structured memo that you could use
in a design or incident-review discussion.

### Practical Exercise: Quantitative Analysis of Specification Ambiguity

Read the following natural-language specification and analyze its ambiguity from
a mathematical perspective:

"A user can log in to the system by entering a valid password. If the password
is incorrect, an appropriate error message is displayed. For security reasons,
consecutive failures are subject to a limit."

**Analysis tasks**
1. **Identify ambiguities**: find at least ten ambiguous points and estimate
   how many plausible interpretations exist for each.
2. **Calculate implementation variation**: compute the theoretical number of
   implementation patterns that arise from the ambiguities you identified.
3. **Assess risk**: rate the potential security risk of each ambiguity on a
   three-level scale.
4. **Prepare for formalization**: prioritize the elements that should be
   addressed using the specification techniques introduced in Chapter 3.

**Suggested output**
- an ambiguity analysis table in any format that lets you compare
  interpretations clearly
- a short note explaining how you estimated the number of implementation
  variants

### Advanced Exercise: Draft an Adoption Plan for Your Own Work

Consider where formal methods could be applied in your current work, or in a
plausible future work setting:

1. **Identify candidate targets**
   - Find the parts of your current systems where formal methods would provide
     the highest value.
   - Estimate the expected benefit quantitatively, such as improved quality,
     development efficiency, or reduced risk.

2. **Create a learning plan**
   - Select the three chapters in this book that are most relevant to your
     work.
   - For each of them, define a concrete action you want to try after studying
     the chapter.
   - Set goals for six months and one year ahead.

3. **Prepare a proposal for your organization**
   - Create presentation material that explains the value of formal methods to
     your manager or peers.
   - Build a business case that explains expected return on investment.

**Suggested output**: a short internal proposal or presentation outline for a
fifteen-minute discussion with peers or managers.

These exercises are designed to deepen both your theoretical understanding of
formal methods and your sense of their practical value. The advanced exercise,
in particular, is intended to serve as both motivation and a roadmap for the
rest of the book. The next chapter moves from motivation to foundations by
showing the natural relationship between programming and mathematics.
