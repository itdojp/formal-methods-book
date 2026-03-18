---
layout: book
title: "Appendix F: Practical Playbook for AI-Assisted Formal Methods"
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-f.md"
---
# Appendix F: Practical Playbook for AI-Assisted Formal Methods

This appendix is a **reader-facing playbook** for using AI assistance without weakening formal assurance. Use it after Chapters 8–12 when you want to turn the book's main argument into a repeatable workflow: let AI draft, let tools judge, and keep the evidence needed for re-verification and review.  
Treat AI output as a proposal, and operate on the assumption that final judgment is delegated to verifiers such as `TLC`, `Alloy`, `Rocq` (formerly `Coq`), and `Dafny`.

## How to Use This Appendix

- **If you are drafting a specification**: start with `F.3 Workflow Template`, then adapt the prompts in `F.4`.
- **If you are handling a counterexample**: jump to `F.6 Minimal Example` and `F.8 Counterexample Triage Template`.
- **If you are preparing a review packet for a team**: use `F.7` and `F.9` together.
- **If you are deciding where AI can and cannot be trusted**: read `F.1` and `F.2` first, then return to Chapters 9–12.

## F.1 Core Working Assumptions

- Generation is fast, but mistakes are fast as well.
- AI is good at generating specifications, invariants, and proof sketches.
- Pass/fail judgment is handled by verifiers and CI.

These assumptions matter because the workflow in this appendix is designed to preserve engineering judgment under acceleration, not to replace that judgment.

## F.2 Trust Boundary and Operating Model

- LLM / agent: **proposer (untrusted)**
- Verifiers (`TLC` / `Alloy` / `Rocq` (formerly `Coq`) / `Dafny`): **judge (trusted)**
- CI: **executor (reproducibility assurance)**

If this boundary is broken, errors from AI flow directly into errors in quality assurance.

## F.3 Workflow Template

1. Clarify the requirement in short sentences, including the objective and prohibited behavior
2. Organize term definitions, including noun boundaries and synonyms
3. Enumerate invariants, that is, properties that must always hold
4. Build a model with small scopes and shallow exploration first
5. Inspect the counterexample and analyze the cause
6. Apply a fix and then rerun verification with reproducibility preserved

In CI, stage the verification depth across pull requests, nightly runs, and pre-release runs so that verification cost remains controlled.

If you only adopt one pattern from this appendix, adopt this workflow and require each step to leave behind evidence that another engineer can rerun.

## F.4 Prompt Templates You Can Adapt (Copy and Paste)

**1) Specification extraction**
```
You are responsible for specifications. From the following requirements, extract term definitions, state, events, invariants, and disallowed behavior.
Requirements: <requirement text>
Output format: terms / state / events / invariants / prohibited behavior
```

**2) Alloy skeleton generation**
```
Convert the following term definitions and invariants into Alloy sig / fact / assert declarations. Make the result a skeleton that can be checked within a small scope.
Terms: <term definitions>
Invariants: <invariants>
```

**3) TLA+ skeleton generation**
```
Using the following state and events, create TLA+ Init / Next / Spec definitions. Include the necessary variables and invariants as well.
State: <state>
Events: <events>
Invariants: <invariants>
```

**4) Counterexample trace summary**
```
Summarize the following counterexample trace and provide three candidate root causes and three candidate fixes.
Counterexample: <trace>
```

**5) Verification checklist for a change review**
```
For the following change, list the verification checkpoints that are required and the commands that should be executed.
Change summary: <change summary>
```

## F.5 Using the Templates in Team Workflows

**When framing a work item**
- Acceptance criteria, expressed in a form whose pass/fail can be judged by verification
- Non-goals, that is, what will not be done
- Execution commands for verifiers and tests

**When reviewing a change**
- Check whether the specification delta and the verification delta are aligned
- Check whether verification logs include the seed, depth, and scope
- Check whether the remediation procedure remains documented when a counterexample appears

These checks are most useful when AI is generating a large share of the draft text, because review otherwise collapses into trust-by-default.

## F.6 Minimal Example: Counterexample → Fix → Re-verification

- Counterexample: a trace is produced that violates FIFO
- Cause: the precondition of the `Dequeue` operation is too weak
- Fix: add an invariant that forbids `Dequeue` on an empty queue
- Re-verification: rerun with the seed, depth, and scope fixed

Read this example together with Chapter 8 or Chapter 10 if you want a compact reminder of the book's core loop: model, check, inspect, fix, and rerun.

## F.7 Review Packet for Team-Based Verification Work

- Verification logs, including the command, seed, depth, and scope
- Counterexample trace, including the file name and reproduction steps
- Change intent, that is, a summary of the requirement or specification delta
- Execution environment, including OS and tool versions

If your team does not use pull requests, attach this packet to the equivalent review gate, such as a design review, release approval, or incident follow-up.

The templates in this appendix can be reused directly as standard operating rules inside a team.

## F.8 Counterexample Triage Template (Separate Facts from Hypotheses)

When processing a counterexample, it is important not to mix facts written in the logs with guesses about the cause.  
AI is useful for summarization and viewpoint enumeration, but the **facts section should be transcribed from logs and traces**, while hypotheses should be placed in a separate section. This separation makes the triage note reusable during review and postmortem analysis.

Use the following as a reusable triage note. If your team keeps a version-controlled template, preserve the same separation between facts, hypotheses, and fixes.

### Template (Copy and Paste)

```
## Verification Target
- Target (specification / implementation / configuration):
- Expected property (safety / liveness / invariant / contract):
- Summary of the change diff:
- Related issue / PR:

## Execution Environment (Facts)
- OS / CPU:
- Execution location (local / CI):
- Tools / versions:
  - Alloy:
  - TLC:
  - Apalache:
  - Dafny:

## Reproduction Steps (Facts)
- command:
- seed:
- scope / depth / length:
- time-limit:
- artifact (logs / counterexample):

## Observed Facts (Excerpt from Logs / Trace)
- Which property was violated:
- Shortest counterexample trace (summary):

## Hypotheses (Candidate Causes)
- H1:
- H2:
- H3:

## Candidate Fixes
- Fix 1:
- Fix 2:

## Re-verification
- Re-execution command:
- Result (OK / NG):
- Lesson learned (prevention for recurrence):
```

## F.9 Quality-Assurance Checklist for AI-Assisted Work Products (Specification / Proof / CI)

When a change includes AI-generated artifacts, turn those artifacts into verifiable work products from the following perspectives.

### Specifications (natural language / Alloy / TLA+)

- Term definitions are clear, including synonyms, boundaries, units, and exception conditions
- Preconditions, such as environmental assumptions, fairness assumptions, and failure models, are stated explicitly
- Invariants, that is, safety properties, are enumerated, and the meaning of a violation can be explained
- Liveness, when required, is defined and does not appear to hold only because of excessive assumptions
- Numerical values, such as percentages, multipliers, and counts, are accompanied by sources or explicitly marked as illustrative examples

### Proof / Model Checking (Reproducibility)

- It is clear what was checked, including the property name, range, and scope / depth / length
- Execution conditions, such as seed, time limit, and exploration bounds, are recorded
- If a counterexample appears, the reproduction steps and the minimal trace remain available
- After applying a fix, the result is re-verified and regression checks are also performed on related properties

### CI (Gate Design)

- Verification depth is staged across pull requests, nightly runs, and pre-release runs
- When a failure occurs, logs and counterexamples are saved as artifacts and remain reproducible
- Conditions for exceptions, such as skipped verification, and the approval flow are defined
- Tool versions are fixed, and caching and reproducibility are preserved
