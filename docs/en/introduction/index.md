---
layout: book
title: "Introduction"
locale: "en"
lang: "en"
source_path: "src/en/introduction/index.md"
---
# Introduction

Many books on formal methods force readers into one of two unsatisfying
choices. Some stay close to mathematics and never fully explain the engineering
payoff. Others focus on a single tool and never show how that tool fits into
the broader landscape. This book is written for readers who need a third
option: a rigorous but practical guide to formal methods as an engineering
discipline.

## What This Book Promises

This book explains how formal specification, model checking, theorem proving,
and program verification relate to each other. It does not assume that readers
will adopt every method. Instead, it helps readers answer practical questions:

- What problem is each method good at?
- What kind of model or property does it require?
- What does the output of the tool or proof attempt actually mean?
- Where is the likely payoff in real development work?

The promise of this book is therefore not “formalize everything.” The promise
is better technical judgment.

## Who This Book Is For

This book is intended for the following readers:

- software engineers and architects who want to reason more precisely about
  behavior, constraints, and assumptions
- quality, testing, and reliability engineers who need stronger techniques for
  high-consequence defects
- practitioners in safety-, security-, or correctness-critical domains
- students and researchers who want a practical entry point into the field

## What This Book Does Not Try to Be

This book is not a certification handbook, a reference manual for one tool, or
a graduate text that expects extensive mathematical maturity before the reader
can make progress. When details matter, it gives enough structure to support
further study, but it remains focused on usable understanding.

## What You Need Before You Start

This book assumes the following background:

- basic programming experience in at least one language
- familiarity with data structures and algorithms
- high-school-level mathematics, especially sets, logic, and functions
- basic knowledge of software requirements, design, and testing

The notation is introduced carefully, so advanced mathematics is not required.

## How the Book Is Organized

The book is organized into four parts and thirteen chapters:

**Part I: Foundations (Chapters 1-3)**  
Why formal methods matter, where informal reasoning breaks down, and what it
means to write a precise specification

**Part II: Methods (Chapters 4-7)**  
Representative specification approaches, including Alloy, Z notation, CSP, and
TLA+

**Part III: Verification (Chapters 8-10)**  
How properties are checked, proved, and connected to program behavior

**Part IV: Practice (Chapters 11-13)**  
How formal methods fit into development processes, toolchains, and case-study
based engineering decisions

## How to Read This Book

If you are new to formal methods, read the book in order at least through
Chapter 8. The later chapters assume that you understand the distinction
between specification, state modeling, and verification properties.

If you already work with one technique, read the corresponding chapter together
with Chapters 1-3. That combination usually gives enough context to avoid
treating one notation as a universal solution.

If your primary goal is adoption in industry, do not skip Part IV. A common
failure mode is to understand the theory but underestimate the organizational
constraints around introducing these methods.

### Quick Reading Paths

- **New to formal methods**: start with Chapters 1-3, then continue through
  Chapters 4-8 so that you learn why precise specifications and verification
  properties matter before choosing tools in depth.
- **Adoption in industry**: read Chapters 1-3 first, then move to Chapters
  11-13 and Appendices D-F to plan a pilot scope, review packet, and evidence
  trail.
- **Already using one method**: pair the chapter for your current method with
  Chapters 1-3 and the most relevant verification chapter, then return to Part
  IV when you need rollout guidance.

## How to Use the Examples and Exercises

The examples in this book are intentionally small enough to inspect and modify.
Their purpose is not to simulate full industrial systems. Their purpose is to
make modeling decisions, counterexamples, and proof obligations visible.

The exercises are part of the learning path rather than optional decoration.
If you want lasting understanding, write down your own specifications, run the
tools where possible, and compare your results with the hints and solution
structure in Appendix D.

## Acknowledgements

This book benefited from the work of researchers who built the field,
engineers who brought formal methods into industrial practice, and reviewers
who identified weaknesses in both exposition and examples. Their influence is
visible throughout the book, even where the final responsibility for errors
remains mine.

January 2025

Kazuhiko Ota (ITDO Inc.)
