---
layout: book
title: "Appendix E: References and Web Resources (Paths to Primary Sources)"
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-e.md"
---
# Appendix E: References and Web Resources (Paths to Primary Sources)

> Translation status: full draft  
> Japanese source of truth: `src/ja/appendices/appendix-e.md`

This appendix is an index to the **primary sources** for the formal methods and tools discussed in the main text, including official sites, official repositories, official documentation, and official releases.  
As of January 2026, it reflects naming changes and updates in mainstream tools, such as `Coq` → `Rocq`, `CVC4` → `cvc5`, the `Alloy 6` series, and `Apalache` in the TLA+ ecosystem.

## Policy for Numeric Sources (Book-wide)

- **Reported values (measurements / case data)**: require a source URL to primary or quasi-primary information, such as papers, official blogs, or official reports.
- **Illustrative examples**: state explicitly that they are examples, so that readers do not misread them as generally established values.
- **Uncertain estimates**: avoid them where possible. If one is unavoidable, state that it is uncertain and provide the assumptions, such as scope and measurement conditions.

## 1) Specification (Alloy / TLA+ / Z / CSP)

### Alloy (Alloy 6.x)

- Purpose: describing relational models and searching for counterexamples within a finite scope
- Relevant chapters: Chapter 4, "Introduction to Lightweight Formal Methods — Specification with Alloy"; Chapter 8, "Introduction to Model Checking"
- Primary sources:
  - Official site: <https://alloytools.org/>
  - Releases (`Alloy 6.x`): <https://github.com/AlloyTools/org.alloytools.alloy/releases>

### TLA+ (TLC)

- Purpose: writing state-transition specifications for distributed and concurrent systems and verifying them by exploration with `TLC`
- Relevant chapters: Chapter 7, "Specifying Time — Introduction to TLA+"; Chapter 8, "Introduction to Model Checking"
- Primary sources:
  - Official TLA+ page (Lamport site): <https://lamport.azurewebsites.net/tla/tla.html>
  - `tlaplus/tlaplus` releases (`tla2tools.jar`): <https://github.com/tlaplus/tlaplus/releases>

### Z (Z notation)

- Purpose: rigorously describing state-based specifications with sets, relations, and mappings so they can serve as a basis for review and verification
- Relevant chapters: Chapter 5, "State-Based Specification — Fundamentals of Z Notation"
- Primary sources (implementations and tools):
  - Community Z Tools (`CZT`): <https://czt.sourceforge.net/>
  - `SourceForge` (`CZT` project): <https://sourceforge.net/projects/czt/>

### CSP

- Purpose: handling communication, synchronization, deadlock, and related properties in concurrent processes
- Relevant chapters: Chapter 6, "Process-Centric Specification — Concurrency with CSP"
- Primary sources (tool example):
  - `FDR` (information on the CSP model checker): <https://www.cs.ox.ac.uk/projects/fdr/>

## 2) Model Checking (TLC / Apalache / SPIN / NuSMV)

### Apalache (Additional checking for TLA+, SMT-based)

- Purpose: checking properties of TLA+ specifications through SMT-based exploration and constraint solving, as a complement to `TLC`
- Relevant chapters: Chapter 7, "Specifying Time — Introduction to TLA+"; Chapter 8, "Introduction to Model Checking"; Chapter 12, "Tools and Automation"
- Primary sources:
  - Official site: <https://apalache-mc.org/>
  - `GitHub` (releases / distributions): <https://github.com/apalache-mc/apalache/releases>

### SPIN (Promela)

- Purpose: model checking of concurrent systems written in `Promela`, including counterexample traces
- Relevant chapters: Chapter 6, "Process-Centric Specification — Concurrency with CSP"; Chapter 8, "Introduction to Model Checking"
- Primary sources:
  - Official page (`spinroot`): <https://spinroot.com/spin/whatispin.html>

### NuSMV

- Purpose: model checking over state-transition models, including `CTL` and `LTL`
- Relevant chapters: Chapter 8, "Introduction to Model Checking"
- Primary sources:
  - Official site: <https://nusmv.fbk.eu/>

## 3) Theorem Proving (Rocq / Lean / Isabelle / Agda)

### Rocq (formerly Coq)

- Purpose: proof assistance based on type theory and kernel checking, together with integrated development of proofs and programs
- Relevant chapters: Chapter 9, "Fundamentals of Theorem Proving"
- Primary sources:
  - Official site: <https://rocq-prover.org/>
  - Release example (`9.0.0`): <https://rocq-prover.org/releases/9.0.0>

### Lean (Lean 4)

- Purpose: theorem proving, use of mathematical libraries, and proof automation through tactics
- Relevant chapters: Chapter 9, "Fundamentals of Theorem Proving"
- Primary sources:
  - Official site: <https://lean-lang.org/>
  - `GitHub` (`Lean 4`): <https://github.com/leanprover/lean4>

### Isabelle

- Purpose: proof assistance with `Isabelle/HOL` and related environments, proof documentation, and tool integration
- Relevant chapters: Chapter 9, "Fundamentals of Theorem Proving"
- Primary sources:
  - `GitHub` (mirror): <https://github.com/isabelle-prover/mirror-isabelle>

### Agda

- Purpose: theorem proving and program description based on dependent types
- Relevant chapters: Chapter 9, "Fundamentals of Theorem Proving", as auxiliary context for type theory
- Primary sources:
  - Documentation: <https://agda.readthedocs.io/en/latest/>

## 4) Program Verification (Dafny / Frama-C / CBMC / VeriFast / SPARK)

### Dafny

- Purpose: integrating specification and verification through contracts and automated checking based on SMT
- Relevant chapters: Chapter 10, "Program Verification"; Chapter 12, "Tools and Automation"
- Primary sources:
  - Official site: <https://dafny.org/>
  - `GitHub`: <https://github.com/dafny-lang/dafny>

### Frama-C

- Purpose: static analysis and verification for C, including annotations and plugins
- Relevant chapters: Chapter 10, "Program Verification"
- Primary sources:
  - `GitHub` (distribution / snapshots): <https://github.com/Frama-C/Frama-C-snapshot>

### CBMC

- Purpose: bounded model checking for C and C++, including bug finding, safety checking, and assertions
- Relevant chapters: Chapter 8, "Introduction to Model Checking"; Chapter 10, "Program Verification"
- Primary sources:
  - Official site: <https://www.cprover.org/cbmc/>

### VeriFast

- Purpose: verification based on separation logic for languages such as C and Java
- Relevant chapters: Chapter 10, "Program Verification"
- Primary sources:
  - `GitHub`: <https://github.com/verifast/verifast>

### SPARK (Ada)

- Purpose: contracts, static analysis, and proof for high-assurance `Ada` development, especially in safety-critical contexts
- Relevant chapters: Chapter 11, "Integrating Formal Methods into Development Processes"; Chapter 12, "Tools and Automation"
- Primary sources:
  - Official site: <https://www.adacore.com/sparkpro>

## 5) SMT Solvers (Z3 / cvc5)

### Z3

- Purpose: a foundation for constraint solving and automated reasoning, often used as a backend for verifiers
- Relevant chapters: Chapter 10, "Program Verification"; Chapter 12, "Tools and Automation"
- Primary sources:
  - `GitHub` releases: <https://github.com/Z3Prover/z3/releases>

### cvc5 (successor to the CVC line, formerly CVC4)

- Purpose: an SMT solver often used as the backend of other verification tools
- Relevant chapters: Chapter 10, "Program Verification"; Chapter 12, "Tools and Automation"
- Primary sources:
  - `GitHub`: <https://github.com/cvc5/cvc5>
  - `GitHub` releases: <https://github.com/cvc5/cvc5/releases>
  - Python bindings, when needed: <https://pypi.org/project/cvc5/>

## 6) Industrial Case Studies (Primary and Quasi-Primary Sources)

### Paris Metro Line 14 (B-Method)

- Relevant chapters: Chapter 13, "Case Studies"
- Primary and quasi-primary sources:
  - Clearsy (`Line 14` / `B-Method`): <https://www.clearsy.com/en/the-tools/extension-of-line-14-of-the-paris-metro-over-25-years-of-reliability-thanks-to-the-b-formal-method/>
  - Butler et al. (`FMICS 2020`, Springer chapter): <https://link.springer.com/chapter/10.1007/978-3-030-58298-2_8>

### Amazon s2n (verification of a cryptographic implementation)

- Relevant chapters: Chapter 13, "Case Studies"
- Primary and quasi-primary sources:
  - `AWS Security Blog`: <https://aws.amazon.com/blogs/security/automated-reasoning-and-amazon-s2n/>
  - Galois (verification example with `SAW`): <https://www.galois.com/articles/verifying-s2n-hmac-with-saw>
  - `CAV 2018` (`s2n`/`SAW` report, PDF): <http://www0.cs.ucl.ac.uk/staff/b.cook/CAV18_s2n.pdf>
  - `s2n-tls` (`GitHub`): <https://github.com/aws/s2n-tls>

### Industrial use of TLA+

- Relevant chapters: Chapter 7, "Specifying Time — Introduction to TLA+"; Chapter 13, "Case Studies"
- Primary and quasi-primary sources:
  - Lamport (`Industrial use of TLA+`): <https://lamport.azurewebsites.net/tla/industrial-use.html>
  - `Microsoft Learn` (distributed implementation and consistency in `Cosmos DB`, with a path to TLA+ specifications): <https://learn.microsoft.com/en-us/azure/cosmos-db/global-dist-under-the-hood>
  - `Azure Cosmos DB` (high-level TLA+ specifications): <https://github.com/Azure/azure-cosmos-tla>
  - `Microsoft Research` (video on TLA+ specifications for `Cosmos DB` consistency guarantees): <https://www.microsoft.com/en-us/research/video/tla-specifications-of-the-consistency-guarantees-provided-by-cosmos-db/>
  - Hackett (`ICSE SEIP 2023`, PDF): <https://fhackett.com/files/icse-seip-23-inconsistency.pdf>

## 7) AI and Formal Methods (LLM Assistance: Positioning and Cautions)

LLMs are useful for drafting specifications, proofs, and counterexample interpretations and for assisting exploration. They are **not**, however, a source of final assurance.  
This book recommends treating LLM output as untrusted input and always closing the loop with mechanical verification such as model checking, type checking, or SMT-based verification.

- Representative implementations and evaluation platforms:
  - `Lean Copilot`: <https://github.com/lean-dojo/LeanCopilot>
  - `ProofGym` (`NeurIPS 2025`): <https://neurips.cc/virtual/2025/131121>
  - `APOLLO` (`arXiv`): <https://arxiv.org/html/2505.05758v5>
  - Natural language to formal language (example: `EMNLP 2025`, PDF): <https://aclanthology.org/2025.emnlp-main.1586v2.pdf>

<!-- markdown-link-check-disable-next-line -->
- Reference (quasi-primary): How Amazon Web Services Uses Formal Methods (`CACM`) <https://cacm.acm.org/research/how-amazon-web-services-uses-formal-methods/>
