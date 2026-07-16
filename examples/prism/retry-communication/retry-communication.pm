// Bounded retry communication as a discrete-time Markov chain (DTMC).
//
// Assumptions are deliberately explicit: attempts are independent, every
// attempt succeeds with probability 0.8, and at most three attempts are made.
// These are teaching assumptions, not measured production failure rates.

dtmc

const double P_SUCCESS = 0.8;
const int MAX_ATTEMPTS = 3;

module retry_communication
  // phase: 0 = ready to attempt, 1 = success, 2 = exhausted attempts
  phase    : [0..2] init 0;
  attempts : [0..MAX_ATTEMPTS] init 0;

  [attempt] phase = 0 & attempts < MAX_ATTEMPTS - 1 ->
      P_SUCCESS       : (phase' = 1) & (attempts' = attempts + 1)
    + (1 - P_SUCCESS) :                (attempts' = attempts + 1);

  [attempt] phase = 0 & attempts = MAX_ATTEMPTS - 1 ->
      P_SUCCESS       : (phase' = 1) & (attempts' = attempts + 1)
    + (1 - P_SUCCESS) : (phase' = 2) & (attempts' = attempts + 1);

  // Absorbing terminal states make long-run probabilities well defined.
  [finish] phase = 1 -> (phase' = 1);
  [finish] phase = 2 -> (phase' = 2);
endmodule

label "success" = phase = 1;
label "failure" = phase = 2;
label "done" = phase != 0;

// Count one unit of cost for each communication attempt.
rewards "cost"
  [attempt] true : 1;
endrewards
