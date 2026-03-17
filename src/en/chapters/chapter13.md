# Chapter 13: Case Studies

> Translation status: full draft  
> Japanese source of truth: `src/ja/chapters/chapter13.md`

## 13.1 Methodology for Case Studies: Learning from Success and Failure

### The Value and Significance of Case Studies

A theoretical understanding of formal methods is important, but real progress in applying them depends on learning from both successful and unsuccessful cases. Case studies bridge the gap between theory and practice and provide practical knowledge. That matters especially in a comparatively young technical field such as formal methods, where many of the actual difficulties and effective countermeasures do not become visible from textbook knowledge alone.

The value of case studies lies in understanding **context**. Even when the same technique is used, its effect and its challenges vary greatly depending on the organization, the problem domain, the technical constraints, and the historical moment in which it is adopted. Successful cases show how a technique can be applied effectively, while unsuccessful cases reveal the pitfalls that should be avoided.

### A Framework for Analyzing Cases

Effective case-study work requires a systematic analytical framework. In this chapter, each case is analyzed from the following perspectives.

**Technical perspective**:  
Which formal methods were used, and why were those methods selected? This includes a detailed analysis of the technical challenges, the solutions adopted, and the technical results obtained.

**Organizational perspective**:  
What kind of organizational structure and process supported the introduction? This includes organizational challenges, the approach to change management, and the role of stakeholders.

**Economic perspective**:  
How did investment cost compare with the benefits obtained? This includes the actual ROI and the way it was measured.

**Social perspective**:  
What social impact did the system have, and what role did formal methods play in that impact? This includes evaluating the social value created through improved safety, security, and reliability.

### A Systematic Understanding of Success Factors

**Technical success factors**:

Choosing the right method is the foundation of success. Key elements include the fit between the nature of the problem and the properties of the method, the ease of integration with existing technology, and the match between the method and the team’s skill level.

A staged adoption approach is also important. Instead of attempting a large and highly complex problem immediately, it is usually more effective to start with a small, well-defined problem and then expand the scope gradually.

**Organizational success factors**:

Management commitment is indispensable. Sustained support has to be based not on abstract technical interest, but on a clear understanding of business value.

The distribution of expertise inside the team also matters. Sustainable adoption depends on avoiding overreliance on a single specialist and instead building a structure in which multiple members share the basics and can support one another.

**External factors**:

Regulatory requirements and industry standards can sometimes accelerate the adoption of formal methods. When these external requirements are used appropriately, they help establish the internal legitimacy of the effort.

The maturity of the technical ecosystem also matters. Tool availability, educational resources, and the presence of an expert community all have a major effect on the probability of success.

### Analyzing Failure Patterns

**Technical causes of failure**:

Selecting an excessively complex method often leads to failure. A technique may be theoretically excellent while still being impractical because it is too difficult to master in real projects.

Poor integration with an existing system is another important failure factor. When formal methods are applied separately from the normal development process, practicality declines and sustained use becomes difficult.

**Organizational causes of failure**:

Excessive expectation of short-term results is a common failure pattern. The benefits of formal methods often emerge over the medium or long term, so expecting dramatic short-term gains usually leads to disappointment.

Underestimating resistance to change is another failure factor. Technical merit alone is not enough to overcome organizational resistance; change management is required.

### The Importance of Contextual Factors

Even the same formal method can produce very different results depending on the context in which it is applied.

**Industry characteristics**:  
In safety-critical systems such as aerospace, medicine, and nuclear power, the value of formal methods is clear and the motivation for introduction is strong. In ordinary business applications, by contrast, it can be harder to make the value tangible.

**Organizational scale**:  
Large enterprises can afford specialist teams and long-term investment, while small and midsize organizations need to use limited resources much more efficiently.

**Technical maturity**:  
An organization’s existing engineering capability strongly affects whether it can learn and use formal methods effectively. If the basics of software engineering are not in place, introducing formal methods is difficult.

**Market environment**:  
In highly competitive markets, development speed may dominate, and short-term feature delivery may take priority over the medium-term or long-term value of quality improvement.

### Methods for Comparative Analysis

**Cross-sectional comparison**:  
By comparing the use of formal methods on similar problems in different industries, it becomes possible to understand both the generality and the limits of a given method.

**Time-series comparison**:  
By tracking how one organization develops its use of formal methods over time, it becomes possible to understand learning processes and patterns of continuous improvement.

**Quantitative analysis**:  
Where possible, comparisons should rely on quantitative data—such as development time, defect discovery rate, and cost reduction—rather than subjective impressions alone.

### A Framework for Learning

To learn effectively from case studies, the following framework is useful.

**Pattern recognition**:  
Identify patterns shared by successful cases and patterns shared by failed cases, and extract principles that can be generalized.

**Condition analysis**:  
Analyze in detail the conditions under which a given outcome was achieved and consider whether those conditions can be reproduced elsewhere.

**Constraint understanding**:  
Understand the technical, organizational, and economic constraints in each case, and evaluate applicability under different constraints.

**Innovative elements**:  
Identify novel approaches and unique ideas in each case, and examine whether they can be transferred to other settings.

### Applying the Lessons in Practice

The following guidelines are useful when applying case-study knowledge to real projects.

**Assess similarity**:  
Evaluate the similarity between your situation and the case from multiple angles, and separate what can be transferred from what cannot.

**Plan adaptation**:  
Consider what changes are needed to adapt the success factors of the case to your own context.

**Evaluate risk**:  
Assess the risk that the failure factors seen in the case will emerge in your own environment, and prepare preventive measures.

**Experiment incrementally**:  
Apply what you learned first in small-scale experiments, and then use those results to decide whether a broader rollout is justified.

The following sections apply this analytical framework to concrete cases. Each case comes from a different industry, uses a different technical approach, and sits in a different organizational context. Together they provide a useful basis for understanding both the diversity of formal-methods applications and the challenges involved.

## 13.2 Traffic Systems: Paris Métro Line 14

### Project Overview and Background

Paris Métro Line 14, the Météor line, opened in 1998 as one of the earliest large-scale fully automated metro lines in the world. The project attracted international attention as a representative case in which formal methods were applied successfully to a large-scale safety-critical system.

**Formalization and Scope of Assurance (Summary)**
- Formalized target: the states, operations, and safety constraints of train control, including minimum distance and speed limits
- Methods and tools: the `B-Method`, including refinement, proof obligations, proof support, and the code-generation toolchain
- Verification targets: safety invariants, consistency of refinement, and, within the limits of publicly available information, avoidance of deadlock and livelock
- Guarantees obtained: properties expressed in the formal model and proof obligations were preserved for the proofs and generated artifacts, within the range of public information
- Out of scope and assumptions: the physical environment, sensor failures, and operating procedures were not fully formalized and therefore had to be covered by separate safety design and testing

The central technical challenge was **fully driverless operation**. In conventional metro systems, the driver bears the final responsibility for safety. On Line 14, every safety decision had to be made by software. That requirement called for a level of confidence that ordinary test-centered quality assurance could not provide.

The project lasted for roughly 15 years, with a total development cost of about 200 million euros. Development involved multiple organizations, including `RATP`, Siemens, and Matra, working in an international collaboration structure.

### Specification and Verification with the B-Method

Line 14 adopted the **B-Method**, a state-based formal method developed by Jean-Raymond Abrial. It supports end-to-end development from an abstract specification to implementation through stepwise refinement.

**Why the B-Method was chosen**:

Technical maturity was the decisive factor. In the early 1990s, the `B-Method` already had industrial results behind it and had tool support that was considered usable for large systems.

French technical tradition also mattered. Because Abrial was a French researcher, there was an expectation that technical support and local expertise would be easier to secure in France.

The availability of staged refinement was another major factor. Because a complex traffic-control system could be refined in stages, large-team collaboration became feasible.

**Approach to writing the specification**:

The entire system was decomposed hierarchically, with an appropriate level of abstraction chosen at each layer. The top level described the basic principles of traffic control, the middle levels described concrete control algorithms, and the lowest levels described implementation detail.

Safety requirements were written explicitly as mathematical constraints. Physical constraints such as minimum distance between trains, maximum speed, and emergency stopping distance were handled in a unified way together with system behavior constraints.

Formal verification was run at each specification level so that consistency and safety could be guaranteed mathematically. Particular attention was paid to avoiding deadlock, in which the system stops, and livelock, in which it continues to move without useful progress.

### Development Process and Tool Usage

**Stepwise refinement process**:

The transition from abstract specification to implementation was performed in several stages. By formally proving the correctness of the transformation at each stage, the project established confidence in the final implementation.

To enable parallel development, the system was decomposed into modules with relatively high independence. Contracts at the module boundaries, that is, interface specifications, were defined strictly so that interactions between modules could be controlled.

**Use of the toolchain**:

An integrated environment known as `B-Toolkit` was used to support specification, proof, and code generation in a single workflow. That toolchain made it possible to semi-automate the path from specification to executable code.

Proof-support tooling was used to construct mathematical proofs of critical safety properties. Fully automatic proving remained difficult, but much of the proof work could be automated, allowing engineers to concentrate on the important proof strategies.

### Technical Results and Challenges

**Successful technical elements**:

The largest result was **clarification of the specification**. Ambiguous requirements expressed in natural language were converted into mathematically precise specifications, which made design contradictions and incompleteness visible early.

**Systematic structuring of the design** made it possible to organize a highly complex system into a form engineers could understand. The hierarchical decomposition helped individual engineers focus on their assigned part without being overwhelmed by the full complexity.

**Improved quality** was also observed quantitatively. Compared with earlier metro systems, software-related failures were reduced by roughly 75 percent.

**Difficulties and limits**:

The biggest challenge was the **high learning cost**. Learning the `B-Method` took months, and effective use generally required more than a year of experience. In the early project phases, insufficient expertise reduced development efficiency.

Tool limitations also created difficulties. Compared with current tools, 1990s tools were limited in functionality and often struggled with performance and usability on large systems.

There were also limits to what could reasonably be formalized. Parts of the system—especially those involving human operation or interaction with the physical environment—were difficult or inappropriate to formalize and therefore required a combination of formal and conventional methods.

### Organizational and Process Aspects

**Coordination across multiple organizations**:

In an international consortium, the formal specification acted as a common language. Differences in interpretation across organizations were reduced substantially, and integration problems were easier to manage.

Using formal specifications in contract management also clarified the responsibilities of each organization and the quality criteria for its deliverables. That removed ambiguity from a legal perspective as well.

**Relationship with regulators**:

Formal proof played a decisive role in explaining safety to the French railway safety authorities. Mathematical proof made it possible to demonstrate the safety of the system objectively.

The use of formal methods was also viewed positively in relation to international standards such as `IEC 61508`, helping establish the international credibility of the system.

### Economic Evaluation

**Direct costs**:

Introducing formal methods increased initial development cost by approximately 20 to 30 percent. This included training, tool acquisition, and time spent on proofs.

However, the cost of finding and fixing problems during integration was reduced substantially. Compared with conventional projects, the frequency of severe problems discovered during integration testing fell by about 60 percent.

**Indirect effects**:

Maintenance costs after deployment were also reduced. Clear specifications made the system easier to understand and improved the efficiency of impact analysis when modifications were required.

The higher reliability of the system also reduced opportunity loss caused by service interruptions. Annual downtime fell by roughly 40 percent compared with earlier systems.

### Long-Term Impact and Development

**Technical legacy**:

The success of Line 14 strengthened confidence in the industrial use of formal methods. Afterward, adoption spread to other transport-system projects.

The techniques and processes developed in the project were also applied to other safety-critical systems, including aircraft control and nuclear-plant control.

**Human-capital effects**:

The project trained a large number of specialists in formal methods. Many of them later became central figures in the French formal-methods community.

Cooperation with universities also strengthened educational programs in formal methods and helped establish a basis for training the next generation.

**Influence on industrial standards**:

The use of formal methods came to be recommended in international standards for transport systems. The Line 14 case became an important reference in standardization.

### Implications for the Present Day

**Using technical progress**:

Compared with the 1990s, formal-methods tools have improved dramatically. At the current state of technology, many of the difficulties faced in the Line 14 project would be easier to address.

The combination of formal methods with AI may also improve proof automation and specification quality, reducing learning cost and improving the efficiency of application.

**Expanding application areas**:

The successful Line 14 model is relevant to newer domains such as autonomous vehicles, drone control, and smart cities.

The staged refinement approach established there is also relevant to modern challenges such as IoT and distributed systems.

The Paris Métro Line 14 project remains a landmark case showing that formal methods can be applied successfully to a large and complex system. It achieved comprehensive success not only technically, but also organizationally, economically, and socially, and it remains an important milestone in the practical adoption of formal methods.

## 13.3 Cloud Services: Amazon’s s2n Cryptographic Library

### Project Background and Motivation

Amazon Web Services (AWS) launched the s2n project in 2015 as a representative example of using formal verification on an implementation of the TLS (Transport Layer Security) protocol. The project emerged from the increasing importance of security in cloud services and from the limits of conventional testing.

**Formalization and Scope of Assurance (Summary)**
- Formalized target: the correspondence between specifications and C implementations for selected components, including cryptographic primitives such as HMAC
- Methods and tools: SAW, Cryptol, and related tooling for mechanical checking
- Verification targets: conformance to specification and properties related to boundary conditions such as size handling and error handling
- Guarantees obtained: for the analyzed components, the implementation was shown to conform to the given specification under the stated assumptions, within the range of public information
- Out of scope and assumptions: properties of the full TLS stack and the operational environment, including randomness, the operating system, and the network, still required separate modeling, review, and testing

**The severity of the security risk**:

TLS plays a central role in encrypting internet communication. If its implementation contains vulnerabilities, a large volume of communication becomes exposed to interception or tampering. Past incidents such as Heartbleed and Poodle demonstrate how important implementation correctness is in TLS.

In a large-scale cloud platform such as AWS, a vulnerability in a TLS implementation can affect millions of users directly. A single implementation bug can trigger a global security incident.

**The limits of conventional methods**:

It is difficult to guarantee the correctness of cryptographic protocols with conventional testing alone. Cryptographic properties such as confidentiality, integrity, and authenticity are not directly observable from outside the system, so standard tests are not sufficient.

Code review also struggles to find subtle defects in cryptographic implementation details. Advanced vulnerabilities such as timing attacks and side-channel attacks are particularly hard to uncover through traditional methods alone.

### Design Principles of the s2n Library

**The minimization principle**:

The s2n library adopted a design strategy that reduced the attack surface by minimizing features. Compared with a general-purpose library such as OpenSSL, its functionality was narrower, but the verification boundary became much clearer.

Supported cipher suites were selected carefully, and deprecated or potentially weak legacy mechanisms were not implemented. That reduced both security risk and verification complexity.

**Designing for formalization**:

The library was designed from the start with formal verification in mind. Preconditions and postconditions were made explicit, side effects were minimized, and the implementation was structured to be easier to verify.

Memory safety was treated as a first-class concern, and typical vulnerabilities such as buffer overflows and use-after-free defects were designed out at the architectural level.

### The Formal Verification Approach

**Use of SAW (Software Analysis Workbench)**:

Amazon and Galois used SAW to perform formal verification of the s2n library. SAW can convert the behavior of C code into a mathematical model and verify cryptographic properties.

One of SAW’s distinguishing features is that it can analyze actual C code directly. Rather than verifying only an abstract model, it verifies the implementation itself, reducing the risk of a gap between model and implementation.

**A staged verification strategy**:

Instead of attempting to verify the whole library at once, the team expanded the scope step by step, starting from the most important functions. They first proved the correctness of cryptographic primitives such as AES and HMAC, and then moved on to protocol logic.

At each function level, detailed specifications were written to define input-output relationships, memory-access patterns, and cryptographic properties mathematically.

**Proof of cryptographic properties**:

The team proved that the implementation of a cryptographic algorithm matched its mathematical specification. For example, they proved that the AES implementation produced results equivalent to the NIST standard for all possible inputs.

They also established constant-time execution properties that support resistance to timing attacks. In other words, execution time was shown not to depend on secret input data.

### Technical Results and Findings

**Problems that were discovered**:

During formal verification, several subtle bugs were found that conventional testing had missed. These problems mainly involved boundary cases and unusual inputs, but they could have been exploitable in practice.

Potential vulnerabilities in memory management were also discovered and corrected. These issues did not appear under normal operation, but they could have been abused with malicious input.

**Properties that were proved**:

The correctness of encryption and decryption was established mathematically. For every valid input, the implementation was guaranteed to produce the intended result.

For the analyzed components under the stated assumptions, memory-safety properties were also proved. The absence of vulnerabilities such as buffer overflows, null-pointer dereferences, and use-after-free defects was demonstrated mathematically for those verified parts.

### Integration with the Development Process

**Continuous verification**:

Formal verification was integrated into the continuous integration (CI) process. Whenever code changed, the related proofs were rerun automatically to reduce the risk of regressions.

For critical functions, implementation changes also required updates to the corresponding formal specifications so that specification and implementation would remain synchronized.

**Coordination with the development team**:

Formal-verification specialists worked closely with implementation engineers to balance verifiable implementations against implementable specifications.

Regular review meetings were used to share verification progress and discovered issues and to adjust development direction as needed.

### Trade-Offs with Performance

**Design decisions that favored verifiability**:

The project deliberately favored verifiability over maximum performance optimization. Simpler, more provable implementations were preferred over more complex high-performance ones.

At the same time, the library still had to satisfy the baseline performance requirements of AWS, so the design balanced practical usability against verification needs.

**Constraints on optimization**:

Common optimization techniques, such as loop unrolling or aggressive branch optimization, can make formal verification harder. s2n therefore used optimization only where verifiability could still be preserved.

The requirement of constant-time execution ruled out many ordinary optimization techniques. This is a textbook example of the trade-off between security and performance.

### Impact on Industry

**Open-source release**:

The s2n library and the results of its formal verification were released as open source. That made it possible for other organizations to benefit from the same high-quality cryptographic implementation.

The verification technique and tooling, including SAW, were also made public, contributing to broader adoption of formal verification technology.

**Influence on industry standards**:

The success of s2n helped establish the importance of formal verification for cryptographic implementations. After that, other major cryptographic libraries also began considering formal verification.

Standardization bodies such as NIST have also been advancing guidance related to formal verification of cryptographic implementations.

### Economic Evaluation

**Increase in development cost**:

Introducing formal verification increased development cost by roughly two to three times. That included learning costs, development and improvement of verification tools, and time spent on proof work.

**Quantifying security value**:

For a large-scale service such as AWS, the cost of a security incident can be enormous. A single vulnerability can plausibly lead to losses worth hundreds of millions of dollars, which makes the value of formal verification extremely high from a risk perspective.

Formal verification also provides significant value by supporting continued customer trust.

### Challenges and Limits

**Limited scope of application**:

The s2n effort focused on selected cryptographic implementations rather than the full TLS protocol or the entire surrounding system. Stronger end-to-end assurance would require a broader verification scope.

**Required expertise**:

Formal verification in this area requires a combination of expertise in cryptography, formal methods, and systems programming. Securing and training that kind of talent remains difficult for many organizations.

### Implications for the Future

**Progress in automation**:

As AI and machine learning continue to advance, more of the work that was manual in the s2n project may become automatable. That would reduce cost and widen practical adoption.

**Expansion to other domains**:

The methods established in s2n are also relevant to other security-critical software, including authentication systems, payment systems, and privacy-preserving systems.

Amazon’s s2n project is an important example showing that formal methods can deliver practical value in large-scale systems of the cloud era. As security requirements keep rising, this kind of approach is becoming increasingly important.

## 13.4 Distributed Systems: Microsoft’s Use of TLA+

### The Complexity and Challenges of Distributed Systems

Microsoft operates large distributed systems such as `Azure`, `Office 365`, and `Xbox Live`, and it has used `TLA+` strategically in the design and verification of such systems. Because distributed systems inherently involve **nondeterminism** and **partial failure**, conventional verification methods alone often struggle to provide sufficient assurance.

**Formalization and Scope of Assurance (Summary)**
- Formalized target: state, transitions, and invariants at the algorithm and design level, with implementation detail abstracted away
- Methods and tools: `TLA+` and `TLC`, used primarily for design review by searching for counterexamples
- Verification targets: safety as invariants, liveness as responsiveness, and fairness assumptions where required
- Guarantees obtained: within the abstract model and the chosen exploration conditions, including finiteness bounds, depth bounds, and fairness assumptions, concrete counterexamples could be found mechanically when a property was violated
- Out of scope and assumptions: implementation bugs such as memory errors or unsafe optimizations, and properties of the operational environment, still had to be covered by other techniques such as testing, static analysis, and proof

**Problems specific to distributed systems**:

Race conditions arise when multiple processes access a shared resource concurrently. Unit and integration testing cannot realistically cover every possible interleaving.

In partial failure, some parts of the system fail while others continue to run. Preserving consistency under those conditions is complex and needs careful design.

Distributed consensus is a difficult problem because multiple nodes must reach the same decision even when network partitions and multiple failures occur.

### Why TLA+ Was Chosen and How It Spread Inside Microsoft

**Introduction of `TLA+` at Microsoft** began in the late 2000s. At first it was used informally by a small number of researchers and senior engineers, but concrete successes gradually led to broader organizational adoption.

**The influence of Leslie Lamport**:

An important enabler was that Leslie Lamport, the creator of `TLA+`, worked at Microsoft Research. Internal technical support and continued improvement of the method were therefore accessible.

Lamport’s internal seminars and technical guidance also helped communicate the value of `TLA+` and the way to apply it effectively.

**Its fit for distributed systems**:

`TLA+` is well suited to expressing the temporal properties of distributed systems. Concepts such as “eventually,” “always,” and “next” map naturally to distributed-system requirements.

Modeling systems as state-transition systems also fits distributed algorithms well.

### Major Application Cases

**Azure Service Fabric**:

`Service Fabric` is a distributed execution platform underpinning parts of `Azure`. It manages service placement, load balancing, and failure recovery across clusters containing thousands of nodes.

By writing `TLA+` specifications, Microsoft verified the correctness of complex cluster-management algorithms. In particular, they used the approach to design and validate algorithms that prevent data loss and service stoppage during node failures.

**Cosmos DB**:

`Cosmos DB` is a globally distributed database service. It manages data across geographically distributed regions while balancing consistency, availability, and partition tolerance.

`TLA+` was used to verify the correctness of complicated replication protocols. In particular, Microsoft analyzed in detail how consistency levels should be adjusted when network partitions occur.

**Xbox Live matchmaking**:

The `Xbox Live` matchmaking service provides real-time game matching for millions of concurrent users. It needs to satisfy fairness, efficiency, and scalability at the same time.

`TLA+` was used to verify designs that guaranteed both fairness and efficiency in the matchmaking algorithm. Particular attention was paid to preventing performance degradation under high load.

### The Approach to Design Verification

**Level of abstraction**:

At Microsoft, `TLA+` is applied primarily to the **essential properties of algorithms**, not to implementation details. Programming-language specifics and performance optimizations are deliberately left out so that attention can remain on logical correctness.

**Stepwise refinement**:

Work starts from high-level requirements and gradually moves toward more detailed algorithms. At each stage, important properties such as safety, liveness, and fairness are checked.

**Verification through model checking**:

The team uses `TLC`, the `TLA+` model checker, to perform exhaustive checking within a finite state space. Real distributed systems are unbounded, but carefully chosen abstractions allow useful finite models to be checked.

### Organizational Strategy for Use

**Engineer training programs**:

Microsoft has run continuing `TLA+` training programs for distributed-systems engineers. These programs cover both the basic concepts and the practical use of the method.

**Building a technical community**:

An internal `TLA+` user community was created to promote experience sharing and mutual assistance. Regular study sessions, case presentations, and question-and-answer exchanges helped accumulate and distribute knowledge.

**Use in design reviews**:

For important distributed systems, creating a `TLA+` specification became part of the standard design-review process. This reduced ambiguity in design and improved the efficiency and quality of review.

### Problems Found and Improvements Achieved

**Finding problems during design**:

Many design-level issues were discovered while writing `TLA+` specifications and checking them. Many of these problems were subtle and depended on complex conditions, making them difficult to find during implementation or testing.

For example, in an early design of `Azure Service Fabric`, a particular timing of node failure could lead to duplicated placement of a service. `TLA+` verification exposed the issue, and the design was corrected.

**Optimizing algorithms**:

Analysis with `TLA+` also helped the team create new algorithms that were safer and more efficient than earlier ones. Mathematical analysis made it possible to improve both performance and correctness at the same time.

### Relationship to Implementation

**Providing guidance for implementation**:

A `TLA+` specification provides the implementation team with a clear design reference. By reproducing the specified state transitions and invariants faithfully in the implementation, design quality can be carried into the code.

**Complementing implementation verification**:

`TLA+` focuses on algorithm-level verification. Implementation details such as memory management, performance optimization, and exception handling still need to be covered by conventional testing and other methods.

### Economic and Organizational Effects

**Improved development efficiency**:

Finding problems at the design stage substantially reduced rework later. This effect was particularly important because integration testing for distributed systems is extremely expensive.

**Systematizing knowledge**:

`TLA+` specifications helped systematize knowledge about complex distributed algorithms and made it easier to share and reuse that knowledge across the organization. New projects could build on existing verified algorithms instead of starting from scratch.

**Technical competitiveness**:

Using formal methods helped Microsoft develop more reliable distributed systems faster than competitors in some critical areas, strengthening technical competitiveness.

### Challenges and Limits

**Limited scope of assurance**:

`TLA+` can establish correctness at the algorithm level, but it does not by itself guarantee implementation detail or performance behavior. Full quality assurance requires a combination of methods.

**Required expertise**:

Using `TLA+` effectively requires both theoretical understanding of distributed systems and strong mathematical reasoning. Not every engineer can operate at the same level immediately.

**Tool limitations**:

Because of the performance limits of `TLC`, directly checking very large systems is difficult. Teams therefore need skill in building abstractions that reduce a system to a tractable model.

### Analysis of the Success Factors

**Management understanding**:

A major foundation of success was that Microsoft’s technical leadership understood the long-term value of formal methods and continued investing in them.

**Staged introduction**:

Instead of applying `TLA+` everywhere at once, Microsoft widened the scope gradually by accumulating successful cases. That supported organizational acceptance.

**A focus on practicality**:

Rather than pursuing academic perfection, the organization emphasized limited but concrete practical value. That made continued internal support easier to sustain.

### Future Outlook

**Advances in automation**:

Progress in AI and machine learning may make `TLA+` specification writing and verification more automated. That could allow more engineers to benefit from formal methods.

**Extension to cloud-native systems**:

Design verification with `TLA+` is likely to spread further into modern cloud-native technologies such as containers, microservices, and serverless systems.

Microsoft’s use of `TLA+` shows that formal methods can provide practical value in improving the design quality of large distributed systems. It is a useful reference for other organizations because it combines organizational commitment with staged adoption to create a durable technical advantage.

## 13.5 Embedded Systems: Automotive Control Systems

### Safety Requirements in the Automotive Industry

The automotive industry is one of the most successful domains for the practical use of formal methods. Automotive electronic control systems are safety-critical systems that directly affect human life, and conventional testing-centered quality assurance alone cannot provide sufficient confidence. The growth of autonomous-driving technology has made software both more important and more complex.

**Formalization and Scope of Assurance (Summary)**
- Formalized target: control logic expressed as state and data flow, together with safety requirements such as invariants, boundary conditions, and degraded-mode behavior
- Methods and tools: executable models such as `SCADE`/`Lustre` and `Simulink`, combined with analysis and verification techniques including static analysis, model checking, and proof support
- Verification targets: absence of runtime errors, soundness of numeric and boundary behavior, safety of state transitions, and safety under degraded conditions
- Guarantees obtained: within the abstraction level of the model or code handled by the tools and under the stated assumptions, the specified properties were either shown to hold or counterexamples were obtained
- Out of scope and assumptions: physical-environment models, assumptions about sensor failure, and behaviors that can only be confirmed through real-vehicle testing still needed separate safety processes

**The influence of `ISO 26262`**:

`ISO 26262`, which came into force in 2011, organized safety requirements for automotive electronic systems into a coherent international standard. The standard recommends or requires the use of formal methods depending on the `ASIL` (`Automotive Safety Integrity Level`).

At `ASIL-D`, the highest safety level, formal specification and formal verification are strongly recommended and in practice often treated as close to mandatory. This accelerated adoption across the automotive industry.

**Growing complexity**:

Modern cars contain more than 100 `ECU`s (`Electronic Control Unit`s) and run over 100 million lines of software code in total. These systems interact tightly and must achieve real-time behavior together with high reliability.

### `SCADE` (`Safety-Critical Application Development Environment`)

**Design principles of `SCADE`**:

`SCADE`, originally developed by Esterel Technologies in France and now part of Ansys, is a development environment for safety-critical systems. It combines visual programming based on dataflow models with formal verification.

Its core concept is the **executable specification**. The model functions at the same time as a specification and as an executable program, which enables simulation, verification, and code generation to be handled in one integrated flow.

**The synchronous dataflow language `Lustre`**:

The theoretical basis of `SCADE` is `Lustre`. `Lustre` is a synchronous dataflow language that can describe the behavior of real-time systems with mathematical precision. Because the concept of time is built into the language, it fits control systems in which real-time behavior is critical.

### Application Cases at Automotive Manufacturers

**ESC development at Bosch**:

`ESC` (`Electronic Stability Control`) is a safety system that prevents vehicle skidding. Bosch used `SCADE` to develop the control algorithm for `ESC` and used formal verification to establish safety properties.

The development process started by expressing high-level control requirements as `SCADE` models. These models included physical vehicle properties such as mass, center of gravity, and tire characteristics, together with control goals such as stability preservation and avoidance of excessive intervention.

Through formal verification, Bosch established mathematically that the system remained safe across possible driving situations. In particular, it verified degraded but safe behavior under sensor failures and communication errors.

**ABS development at Continental**:

`ABS` (`Anti-lock Braking System`) prevents wheel lock during hard braking. Continental combined `SCADE` and `Polyspace` to develop and verify `ABS` software.

`SCADE` was used for the control logic, while `Polyspace` was used for implementation-level static analysis. This combination supported assurance at both the algorithm level and the implementation level.

A particularly important point was verification of the algorithm that prevents error accumulation in wheel-speed sensor signal processing. Formal methods were used to show that numerical error would not accumulate enough to affect control performance.

### Use at Japanese Automotive Manufacturers

**Toyota’s use of formal methods**:

Toyota has used formal methods in the energy-management systems of hybrid vehicles. These systems require complex control algorithms that reconcile fuel efficiency with vehicle performance by coordinating the engine and motor.

Toyota uses a development environment centered on `MATLAB/Simulink` and integrates formal-verification tools into that environment. Formal methods have played an important role in verifying algorithms that balance conflicting goals such as battery protection and performance optimization.

**Honda’s application of ASIMO technology to automobiles**:

Honda has applied control technology developed for the humanoid robot `ASIMO` to automotive systems. In particular, it has worked on systems that combine human-behavior prediction with vehicle control for pedestrian-collision mitigation.

When modeling complex human behavior, formal methods have been used to assess the validity of prediction algorithms. Human behavior is inherently difficult to predict, but formal methods help define conservative control strategies that preserve safety.

### Practice at Tier 1 Suppliers

**Integrated ECU development at Denso**:

Denso has established an `AUTOSAR`-compliant formal development approach for ECUs that integrate multiple functions.

When multiple safety-critical functions such as braking, steering, and engine control are executed on a single ECU, Denso uses formal verification to analyze both independence and safe interaction between those functions.

In particular, it proves the absence of race conditions on shared resources such as CPU, memory, and communication buses, and it verifies satisfaction of real-time constraints.

**Bosch’s ADAS platform**:

In advanced driver-assistance systems (`ADAS`), Bosch develops systems that integrate signals from multiple sensors—such as cameras, radar, and `LiDAR`—to make appropriate control decisions.

Formal methods are used to design and verify algorithms for evaluating sensor reliability and for making safe control decisions under uncertainty.

### Transformation of the Development Process

**Establishing model-based development**:

The automotive industry has been shifting from code-centered development to model-centered development. With tools such as `SCADE` and `MATLAB/Simulink`, automatic code generation from executable models has become standard practice.

This shift makes it possible to verify systems earlier in the design phase and significantly reduces the cost of discovering and correcting problems late in development.

**Formalizing the V-model process**:

The traditional V-model development process—from requirements definition to design, implementation, and testing—has been extended with formal verification. Formalizing the artifacts at each stage improves both traceability and quality assurance across the full process.

### Regulatory Compliance and Certification

**Use in type approval**:

In automotive type approval, formal-verification results have become important evidence. In particular, authorities in Europe and Japan evaluate formal verification of safety-critical functions positively.

**Effect on recall prevention**:

Systems developed with formal methods have been shown statistically to have significantly lower recall rates. This is important not only from a quality standpoint, but also from an economic one.

### Challenges and Future Development

**Managing complexity**:

As autonomous-driving technology develops, the complexity of control systems continues to increase. The integration of machine learning and AI creates challenges that conventional formal methods alone cannot easily address.

**Combining with new technologies**:

Research is advancing on hybrid approaches that combine deep-learning-based environment recognition with control decisions validated through formal methods.

**Integrating cybersecurity**:

As connected cars become more common, security requirements are becoming as important as safety requirements. A major challenge is to develop methods that can provide formal assurance for both safety and security.

### Spillover Effects Across Industry

**Impact on aerospace**:

The formal-methods practices established in the automotive industry have influenced aerospace as well. Automotive success cases have contributed significantly to the strengthening of the role of formal methods in `DO-178C`.

**Application to medical devices**:

Methods established in automotive systems are also being applied to medical-device control systems. Experience from the automotive field has informed recommendations in standards such as `IEC 62304` for medical-device software.

The success of formal methods in the automotive industry is an important case demonstrating their effectiveness in the development of safety-critical systems. Because regulatory requirements, technical necessity, and economic value align in this domain, organizations have been able to sustain adoption and continuous improvement.

References (semi-primary and overview sources):
<!-- markdown-link-check-disable -->
- `ISO 26262` (overview): <https://en.wikipedia.org/wiki/ISO_26262>
- `SCADE` (background: Esterel Technologies): <https://en.wikipedia.org/wiki/Esterel_Technologies>
- `Lustre` (synchronous dataflow language): <https://en.wikipedia.org/wiki/Lustre_(programming_language)>
- `Polyspace` (static analysis tool): <https://en.wikipedia.org/wiki/Polyspace>
<!-- markdown-link-check-enable -->

## 13.6 Lessons Learned and Guidance for the Future

### Common Patterns Extracted from the Successful Cases

When the cases discussed so far—Paris Métro Line 14, Amazon s2n, Microsoft’s use of TLA+, and automotive control systems—are analyzed side by side, clear common patterns emerge.

**A clear problem definition and motivation**:

In every successful case, formal methods were introduced to solve a concrete problem. On the Paris Métro project, the issue was fully autonomous operation. In s2n, it was removal of security vulnerabilities. At Microsoft, it was the design quality of distributed systems. In automotive systems, it was the need to assure safety. In each case, the triggering issue was concrete and urgent.

This is a critical lesson. Formal methods do not achieve organizational success on the basis of academic interest alone. Their real power emerges when they are tied to clear business value or social value.

**Staged and strategic introduction**:

Every successful case used a staged introduction strategy. Rather than tackling the most complex problem from the start, each organization began with clearer and more manageable problems and only then expanded the scope.

For Paris Métro Line 14, development began with basic control logic and gradually extended to more complex integrated control. At Microsoft, use began from individual interest, moved through small project successes, and eventually became part of organizational strategy.

**Appropriate technical choice and realistic expectations**:

Successful cases did not choose the theoretically “best” technique in the abstract. They chose the method that best fit the situation. Practicality mattered more than perfection, and the selected technique matched both the problem domain and the organization’s maturity.

The methods differed—B-Method, SAW, TLA+, and SCADE—but all were selected because they fit the target problem and the technical maturity of the organization.

### Learning from Failure Patterns

Just as successful cases are instructive, unsuccessful cases also provide important lessons. Many failures share common causes.

**The limits of a technology-first approach**:

Projects often fail when they choose the newest or most theoretically sophisticated technology while neglecting organizational readiness and real-world constraints. Technical excellence and practical success do not necessarily correlate.

**Excessive expectations and short-term evaluation**:

When organizations set unrealistic expectations for formal methods and demand dramatic short-term improvements, early difficulty often leads to abandonment. The value of formal methods often appears over a longer horizon.

**Neglect of change management**:

If attention is focused only on technical issues while organizational culture and human factors are neglected, technical success may still fail to become sustained organizational practice.

### Application Characteristics by Industry

**The relative advantage of safety-critical domains**:

In safety-critical domains such as aerospace, automotive, rail, and medical devices, the value of formal methods is easier to demonstrate and the return on investment is often higher. When regulatory requirements exist, the motivation is even stronger.

**Growth in finance and security**:

With the spread of cloud services and the rising importance of cybersecurity, the use of formal methods is expanding rapidly in finance and security.

**Challenges in ordinary business applications**:

In general business applications without direct safety or security requirements, it is often harder to make the value of formal methods tangible, and adoption success rates tend to be lower.

### Technical Progress and Future Outlook

**Advances in automation**:

As AI and machine learning advance, many of the manual tasks in formal methods are becoming easier to automate. Support for writing specifications, automating proofs, and analyzing counterexamples may all become accessible to a broader range of engineers.

**Maturing tools and better integration**:

The usability of formal-methods tools and their integration with existing development environments have improved substantially. This should reduce learning cost and lower the barrier to introduction.

**Demand from new technical domains**:

New fields such as IoT, blockchain, autonomous driving, AI, and quantum computing raise challenges that conventional quality-assurance approaches struggle to address. That is increasing demand for formal methods.

### Systematizing Organizational Success Factors

**The importance of leadership**:

Without exception, successful cases involve strong commitment from both technical and organizational leaders. It is essential to sustain support through short-term difficulty and pursue long-term value creation.

**Talent development and knowledge management**:

A suitable talent-development strategy is indispensable. Sustainable use depends on moving from dependence on external experts to internal capability, and from individual knowledge to organizational knowledge.

**Stepwise realization of value**:

It is more effective to accumulate small value incrementally than to attempt to realize all the value at once. Early successes help secure internal support and continued investment.

### Practical Guidance for Application

**Assess the current state and readiness**:

An organization considering formal methods should first evaluate its current technical maturity, cultural readiness, and clarity of the problem it is trying to solve. Forcing adoption before the organization is ready increases the risk of failure.

**Choose an appropriate adoption strategy**:

It is important to select an adoption strategy that fits the organization’s circumstances. Combining top-down, bottom-up, and externally supported approaches can improve the probability of success.

**Build a structure for continuous learning and improvement**:

Introducing formal methods is not a one-time event. It is a continuing process of learning and improvement. Regular measurement of results, identification of problems, and execution of countermeasures are all necessary to keep improving organizational capability.

### Social Impact and Responsibility

**The changing social role of software**:

Software is no longer merely a tool; it has become part of social infrastructure. As a result, the social responsibility of software engineers has also changed significantly. Formal methods are one important means of meeting that responsibility.

**Professional responsibility of engineers**:

As with physicians and architects, software engineers increasingly carry professional responsibility and ethical obligations. Learning and applying formal methods is becoming part of that professional duty.

**Addressing the digital divide**:

The benefits of formal methods should not remain concentrated in a small number of organizations or regions. Educational institutions, open-source communities, and international collaboration all play a role in spreading knowledge and technique more broadly.

### Directions for Future Research and Development

**The importance of interdisciplinary research**:

Further progress in formal methods will require not only computer science, but also mathematics, logic, cognitive science, and sociology. Work is needed not just on technical questions, but also on human-computer collaboration, integration with social systems, and ethical considerations.

**Strengthening industry-academia collaboration**:

To bridge the gap between theory and practice, stronger collaboration between industry and academia is essential. Mechanisms are needed both for research grounded in real industrial problems and for transferring research outcomes back into practice.

**Promoting international cooperation**:

The development and diffusion of formal methods cannot be achieved by a single country or a single organization alone. International cooperation is needed through standardization, researcher exchange, and technology transfer.

### Conclusion: Expectations for the Future of Formal Methods

What these case studies make clear is that formal methods are not merely an academic topic. They are practical techniques for solving real and complex problems. At the same time, successful use depends on appropriate technical choice, organizational preparation, staged introduction, and continuous improvement.

As digitalization advances and software becomes even more socially important, demand for formal methods is likely to keep increasing. At the same time, the progress of AI may make formal methods easier to apply and available to a much wider range of organizations and individuals.

The important point is not to treat formal methods as a universal solution. Their value comes from understanding both their strengths and their limits and using them effectively in the right places. If organizations learn from these successful cases and adapt the lessons to their own situation, they can improve software quality and create broader social value.

---

## End-of-Chapter Exercises

### Reading Check Exercise 1: Comparative Analysis of the Cases

Compare the four cases discussed in this chapter—Paris Métro Line 14, Amazon `s2n`, Microsoft’s use of `TLA+`, and automotive control systems—from the following perspectives.

**Analytical viewpoints**:
1. **Technical factors**:
   - The formal method selected and why it was chosen
   - The technical challenges and how they were addressed
   - The technical results obtained

2. **Organizational factors**:
   - The trigger for introduction and the promotion structure
   - The approach to change management
   - Talent development and knowledge management

3. **Economic factors**:
   - Scale of investment and payback period
   - Direct and indirect effects
   - Risk-reduction effects

4. **External factors**:
   - The influence of regulatory requirements and industry standards
   - The impact of the competitive environment
   - Social expectations and responsibility

**Deliverables**:
- A comparison table summarizing the characteristics of each case
- An analysis of common success factors and important differences
- A discussion of failure risks and ways to mitigate them
- An evaluation of applicability in other contexts

### Reading Check Exercise 2: Industry Applicability Analysis

Using the cases in this chapter as reference points, analyze the applicability of formal methods in the following industries.

**Target industries** (choose one or two):
- Healthcare and medical devices
- Finance and fintech
- Energy and smart grids
- Telecommunications and `5G/6G` networks
- Robotics and industrial automation

**Analysis items**:
1. **Industry characteristics**:
   - Level of safety and security requirements
   - Regulatory environment and standardization status
   - Technical complexity and constraint conditions

2. **Value of applying formal methods**:
   - Expected effects and value
   - Comparative advantages over conventional methods
   - Expected return on investment

3. **Adoption challenges and barriers**:
   - Technical challenges
   - Organizational and cultural barriers
   - Economic constraints

4. **Proposal for an adoption strategy**:
   - A staged adoption plan
   - Technical selection guidelines
   - Risk-mitigation measures

### Practical Exercise 1: Detailed Case Investigation

Choose one of the cases discussed in this chapter and investigate it in more detail.

**Investigation methods**:
- Review academic papers and technical reports
- Interview related stakeholders if feasible
- Compare the case with similar cases
- Investigate the latest developments related to the case

**Investigation items**:
1. **Background and motivation in detail**:
   - The situation at the start of the project
   - The decision-making process
   - Stakeholder relationships

2. **Technical detail**:
   - The methods used in detail
   - The technical challenges and how they were solved
   - Details of tools and environments

3. **Organizational aspects**:
   - Team composition and role allocation
   - The content of education and training
   - The internal consensus-building process

4. **Results and impact**:
   - Quantitative and qualitative outcomes
   - Long-term influence and subsequent development
   - Spillover effects into other projects

**Suggested outputs**:
- A detailed investigation report of 20 to 30 pages
- An analysis of success factors and remaining challenges
- A proposal for how the lessons could be applied in other organizations

### Practical Exercise 2: Designing an Adoption Plan

Create a concrete plan for introducing formal methods into a real or hypothetical organization.

**Assumptions**:
- Organization size: 20 to 100 developers
- Industry: a domain in which safety or security is important
- Current state: conventional development methods are in use
- Goal: improve quality and strengthen competitiveness

**Plan elements**:
1. **Current-state analysis**:
   - Evaluation of technical maturity
   - Analysis of organizational culture
   - Identification of problems and risks

2. **Strategy design**:
   - A staged three-year adoption plan
   - A technology-selection strategy
   - An investment plan and ROI analysis

3. **Execution plan**:
   - Design of a pilot project
   - Education and training program
   - Organizational change-management plan

4. **Risk management**:
   - Identification of major risks
   - Mitigation measures and a contingency plan
   - Success indicators and evaluation methods

**Suggested output**: a concise management proposal or presentation outline
that could be used to discuss adoption with decision-makers

### Advanced Exercise: Future-Scenario Analysis

Analyze possible development scenarios for formal methods over the next ten years and derive strategic implications.

**Analytical viewpoints**:
1. **Technical development**:
   - Integration with AI and machine learning
   - Increasing automation and sophistication of tools
   - Application to new technical domains

2. **Industry trends**:
   - Changes in the regulatory environment
   - Changes in competitive structure
   - Emergence of new application fields

3. **Social factors**:
   - Progress of digitalization
   - Security and privacy requirements
   - Software as social infrastructure

4. **Education and talent**:
   - Changes in university education
   - The need for continuing education
   - The supply-demand balance for specialist talent

**Scenario design**:
- An optimistic scenario, with rapid diffusion
- A realistic scenario, with staged growth
- A pessimistic scenario, with stagnation or retreat

**Strategic implications**:
- Response strategies under each scenario
- Implications for investment decisions
- Recommendations for policy and education

**Deliverables**:
- A scenario-analysis report
- A discussion of the strategic implications
- A policy recommendation document

Through these exercises, use the knowledge gained from case studies in practical settings and develop the ability to assess and use the strategic value of formal methods. In the advanced exercise in particular, take a long-term view of the future of formal methods and aim to develop the insight needed to contribute to that future.
