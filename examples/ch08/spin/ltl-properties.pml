bool critical_section = false;
bool cs1 = false;
bool cs2 = false;

active proctype Worker() {
  do
  :: critical_section = true;
     critical_section = false
  od
}

active proctype P1() {
  do
  :: atomic { !cs2 -> cs1 = true; cs1 = false }
  od
}

active proctype P2() {
  do
  :: atomic { !cs1 -> cs2 = true; cs2 = false }
  od
}

ltl fairness { []<>(critical_section) }
ltl mutual_exclusion { [](!(cs1 && cs2)) }
