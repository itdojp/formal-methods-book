---- MODULE Queue ----
EXTENDS Naturals, Sequences

VARIABLES q

Init == q = << >>

Enqueue(x) == q' = Append(q, x)
Dequeue == q # << >> /\ q' = Tail(q)

Next == \E x \in Nat: Enqueue(x) \/ Dequeue

Spec == Init /\ [][Next]_<<q>>

====
