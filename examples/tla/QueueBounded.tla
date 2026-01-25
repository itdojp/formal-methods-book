---- MODULE QueueBounded ----
EXTENDS Naturals, Sequences

\* A tiny, finite-state queue example for TLC/Apalache.
\* - Values is a finite set (configured in .cfg)
\* - Queue length is bounded by MaxLen (configured in .cfg)

CONSTANTS MaxLen, Values
VARIABLES q

Init == q = << >>

Enqueue(x) ==
  /\ x \in Values
  /\ Len(q) < MaxLen
  /\ q' = Append(q, x)

Dequeue ==
  /\ q # << >>
  /\ q' = Tail(q)

Next == (\E x \in Values: Enqueue(x)) \/ Dequeue

Spec == Init /\ [][Next]_<<q>>

Inv == Len(q) <= MaxLen

====
