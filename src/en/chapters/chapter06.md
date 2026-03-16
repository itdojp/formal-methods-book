# Chapter 6: Process-Centric Description: Concurrent Systems with CSP

> Translation status: overview draft  
> Japanese source of truth: `src/ja/chapters/chapter06.md`

This English page summarizes the Japanese chapter and highlights the main ideas
behind CSP. It is not yet a section-by-section translation.

## Why This Method Matters

Concurrency becomes difficult when behavior depends on interaction, scheduling,
partial failure, and synchronization rather than on a single sequential flow.
CSP provides a process-oriented view that makes communication and coordination
explicit, which is why it remains valuable for protocol design and concurrent
system analysis.

## Core Ideas

- **Processes and events are first-class concepts**: systems are described as
  processes that engage in events, rather than as hidden internal state alone.
- **Communication structure matters**: channels, synchronization points, and
  composition operators determine whether the system can progress safely.
- **Nondeterminism is normal**: CSP does not eliminate scheduling uncertainty;
  it models it explicitly so designers can reason about it.
- **Deadlock and liveness are central concerns**: concurrent designs must be
  judged not only by what they can do, but also by whether they can keep doing
  useful work.

## What This Chapter Covers

- Why concurrency is hard, including interaction complexity and nondeterminism
- The CSP worldview of processes, events, channels, and synchronization
- Basic process expressions such as prefix, choice, parallel composition,
  recursion, hiding, and renaming
- Communication patterns, coordination protocols, and structured process
  composition
- Deadlock, livelock, progress, and practical verification targets

## Representative Example

The Japanese chapter develops a restaurant system as an integrated example.
This example combines table management, ordering, kitchen resources, inventory,
payment handling, and emergency situations into one concurrent design. It shows
how CSP can describe both local process behavior and whole-system interaction.

## When to Use CSP

CSP is well suited to systems where the main design risk lies in coordination:
protocols, workflows, message-passing systems, multi-component services, and
resource-sharing scenarios. It is especially useful when you need to ask
whether components can synchronize safely, whether deadlock is possible, and
which communication patterns preserve progress.

## Relationship to Other Chapters

Chapter 6 complements the state-based view of Z by focusing on interaction and
composition. It also prepares the reader for later verification chapters, where
deadlock, liveness, and machine-assisted checking become more explicit
verification tasks.
