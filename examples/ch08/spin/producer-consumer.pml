mtype = { msg };
chan buffer = [1] of { mtype };

active proctype Producer() {
  do
  :: buffer!msg -> printf("Produced\n")
  od
}

active proctype Consumer() {
  do
  :: buffer?msg -> printf("Consumed\n")
  od
}
