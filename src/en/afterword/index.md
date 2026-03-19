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
In practice, readers most often return when one of the following concrete
problems appears:

- **You need to choose a notation or modeling style**: go back to Chapters 3-7
  together with [Appendix C]({{ '/en/appendices/appendix-c/' | relative_url }}).
- **You need to interpret a counterexample, proof obligation, or failure
  report**: return to Chapters 8-10, then use
  [the glossary]({{ '/en/glossary/' | relative_url }}) if the terminology in
  the result needs to be stabilized.
- **You need to plan adoption, review flow, or rollout**: use Chapters 11-13
  with [Appendix D]({{ '/en/appendices/appendix-d/' | relative_url }}) and
  [Appendix F]({{ '/en/appendices/appendix-f/' | relative_url }}).
- **You need to align terminology across team documents**: consult
  [the glossary]({{ '/en/glossary/' | relative_url }}) and
  [Appendix C]({{ '/en/appendices/appendix-c/' | relative_url }}) before
  rewriting the terms in new specifications or review notes.

If the book succeeds as a reference, it should help you restart thinking
quickly rather than forcing you to reconstruct the entire field from memory.

## Choose Your Next Path

The right second pass depends on the kind of problem you need to solve next:

- **Modeling path**: Revisit Chapters 3-7 together with
  [Appendix C]({{ '/en/appendices/appendix-c/' | relative_url }}). Rework one
  small requirement or protocol from your own domain in two different
  notations, then compare what each notation makes visible.
- **Verification path**: Return to Chapters 8-10. Take one property from a
  real component, write it as a candidate invariant or temporal property, and
  record what the first counterexample or proof obligation actually teaches
  you.
- **Adoption path**: Use Chapters 11-13 with
  [Appendix D]({{ '/en/appendices/appendix-d/' | relative_url }}) and
  [Appendix F]({{ '/en/appendices/appendix-f/' | relative_url }}). Define one
  pilot target, one review checkpoint, and one piece of evidence your team
  will expect before trusting the result.

Formal methods reward repeated contact. The first pass gives vocabulary and
structure. The second pass should connect that structure to a real engineering
decision.

## Stay Close to Practice

The field continues to evolve. AI-assisted development, large-scale
distributed systems, safety regulation, and security pressure all increase the
need for precise reasoning. At the same time, no method is valuable merely
because it is mathematically elegant. A method becomes valuable when it helps
teams make fewer wrong assumptions, expose defects earlier, and explain why a
system should be trusted.

That is the standard this book ultimately argues for: not formalism for its
own sake, but rigor where rigor changes outcomes.

## Choose One Next Step for the Next 30 Days

If you want this book to remain useful after the first read, do not start with
an ambitious reading backlog. Choose one of the following next steps and
complete it within the next month:

- **Choose one chapter-aligned source**: Use
  [Appendix E]({{ '/en/appendices/appendix-e/' | relative_url }}) to pick one
  paper, official guide, or book that deepens the chapter you most need next.
- **Choose one pilot target**: Pick one component, workflow, or requirement
  that still feels ambiguous, then use
  [Appendix D]({{ '/en/appendices/appendix-d/' | relative_url }}) and
  [Appendix F]({{ '/en/appendices/appendix-f/' | relative_url }}) to define
  one review checkpoint and one piece of verification evidence you want to see.
- **Choose one terminology checkpoint**: If language is drifting inside your
  team, return to [the glossary]({{ '/en/glossary/' | relative_url }}) and
  [Appendix C]({{ '/en/appendices/appendix-c/' | relative_url }}) before
  writing new specifications, review notes, or design documents.

The point is not to do everything at once. The point is to convert one part of
this book into a repeated practice.

I close this book with a practical expectation: use formal methods where they
change a decision, reduce an ambiguity, or strengthen a claim that matters.

January 2025

Kazuhiko Ota (ITDO Inc.)
