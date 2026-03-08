---- MODULE Counter ----
EXTENDS Integers

\* A small, typed, finite-state spec intended for Apalache.

CONSTANT
  \* @type: Int;
  N

VARIABLE
  \* @type: Int;
  x

Init == x = 0

Next == x' = IF x < N THEN x + 1 ELSE 0

Spec == Init /\ [][Next]_x

Inv == x >= 0 /\ x <= N

====
