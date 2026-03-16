---
layout: book
title: "Appendix F: Practical Guide to Running Formal Specification and Verification with AI Assistance"
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-f.md"
---
# Appendix F: Practical Guide to Running Formal Specification and Verification with AI Assistance

This appendix collects practical templates for running specification work and verification with AI assistance. Treat AI output as a proposal, and operate on the assumption that final judgment is delegated to verifiers such as `TLC`, `Alloy`, `Rocq` (formerly `Coq`), and `Dafny`.

## F.1 Assumptions in the AI Era

- Generation is fast, but mistakes are fast as well.
- AI is good at generating specifications, invariants, and proof sketches.
- Pass/fail judgment is handled by verifiers and CI.

## F.2 Trust Boundary

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

## F.4 Prompt Templates (Copy and Paste)

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

**5) Verification checklist for a pull request**
```
For the following change, list the verification checkpoints that are required and the commands that should be executed.
Change summary: <pull request diff summary>
```

## F.5 Agent Operation Guide

**When creating an issue**
- Acceptance criteria, expressed in a form whose pass/fail can be judged by verification
- Non-goals, that is, what will not be done
- Execution commands for verifiers and tests

**When reviewing a pull request**
- Check whether the specification diff and the verification diff are aligned
- Check whether verification logs include the seed, depth, and scope
- Check whether the remediation procedure remains documented when a counterexample appears

## F.6 Minimal Example: Counterexample → Fix → Re-verification

- Counterexample: a trace is produced that violates FIFO
- Cause: the precondition of the `Dequeue` operation is too weak
- Fix: add an invariant that forbids `Dequeue` on an empty queue
- Re-verification: rerun with the seed, depth, and scope fixed

## F.7 Artifacts That Should Be Attached to a Pull Request

- Verification logs, including the command, seed, depth, and scope
- Counterexample trace, including the file name and reproduction steps
- Change intent, that is, a summary of the specification diff
- Execution environment, including OS and tool versions

The templates in this appendix can be reused directly as standard operating rules inside a team.

## F.8 Counterexample Triage Template (Separate Facts from Hypotheses)

When processing a counterexample, it is important not to mix facts written in the logs with guesses about the cause.  
AI is useful for summarization and viewpoint enumeration, but the **facts section should be transcribed from logs and traces**, while hypotheses should be placed in a separate section.

Template file in the repository: `templates/counterexample-triage.md` (the same content is also reproduced below)

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

## F.9 Quality-Assurance Checklist for AI-Generated Artifacts (Specification / Proof / CI)

When a change includes AI-generated artifacts, reduce it to a verifiable deliverable from the following perspectives.

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
