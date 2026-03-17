# Afterword

You have now moved through the full arc of the book: why formal methods matter,
how specifications are written, how properties are checked or proved, and how
these techniques fit into actual development work. The final question is what
you should do with that knowledge after closing the book.

## What You Should Be Able to Do Now

After working through this book, you should be able to do more than define
formal methods in the abstract. You should be able to make concrete technical
judgments such as the following:

- when an ambiguity in requirements should be turned into an explicit
  specification
- when a lightweight modeling step is likely to be cheaper than debugging late
  in implementation
- when model checking is a better fit than theorem proving, and when the
  reverse is true
- how to read a counterexample, proof obligation, or invariant failure without
  treating the tool as a black box

That shift in judgment is the real payoff of introductory study.

## Adopt Gradually, but Adopt Deliberately

One of the recurring lessons in this book is that successful adoption is
rarely all-or-nothing. Most teams do not start by verifying an entire product.
They start by formalizing one protocol, one concurrency-sensitive component, or
one safety-critical workflow.

The important point is not to keep the scope small forever. The important point
is to choose the first target deliberately: select a part of the system where
ambiguity is expensive, failures are costly, or concurrency makes testing
alone unreliable.

## How to Use This Book After the First Read

This book is intended to remain useful after an initial cover-to-cover read.
In practice, readers often return in the following ways:

- go back to Chapters 3-7 when choosing a modeling style or notation
- return to Chapters 8-10 when interpreting a verification result or planning
  a proof strategy
- use Chapters 11-13 when discussing process design, tool adoption, or
  organizational rollout
- consult Appendix C and the glossary when terminology becomes unstable across
  teams or documents

If the book succeeds as a reference, it should help you restart thinking
quickly rather than forcing you to reconstruct the entire field from memory.

## Where to Go Next

The next step depends on your goals:

- if you want stronger modeling skill, deepen your work in Alloy, Z, CSP, or
  TLA+ through repeated small exercises
- if you want stronger assurance arguments, spend more time on model checking,
  proof assistants, and program verification
- if your goal is organizational change, study the case studies and then pilot
  one narrow but high-value adoption effort in your own context

Formal methods reward repeated contact. The first pass gives vocabulary and
structure. Later passes turn that structure into engineering instinct.

## Stay Close to Practice

The field continues to evolve. AI-assisted development, large-scale
distributed systems, safety regulation, and security pressure all increase the
need for precise reasoning. At the same time, no method is valuable merely
because it is mathematically elegant. A method becomes valuable when it helps
teams make fewer wrong assumptions, expose defects earlier, and explain why a
system should be trusted.

That is the standard this book ultimately argues for: not formalism for its
own sake, but rigor where rigor changes outcomes.

## Resources for Continued Study

If you want to continue learning, the following are practical next steps:

- **Conferences**: FM, CAV, TACAS, ICSE, FSE
- **Journals**: IEEE TSE, ACM TOSEM, SCP, STTT
- **Communities**: the TLA+ community, Alloy users, theorem-proving
  communities, and relevant engineering groups
- **Hands-on follow-up**: replicate one example from this book in your own
  domain, then compare what changed in the model and in the questions you asked

With that, I would like to close this book by wishing you continued growth and
success in the field of formal methods.

January 2025

Kazuhiko Ota (ITDO Inc.)
