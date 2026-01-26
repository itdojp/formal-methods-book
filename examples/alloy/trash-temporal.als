module trashTemporal

sig File {}

-- Make the example non-trivial (otherwise File can be empty by default).
fact { some File }

-- Alloy 6: `var` marks mutable state across a trace.
var sig Trash in File {}

pred delete[f: File] {
  f not in Trash
  Trash' = Trash + f
}

pred restore[f: File] {
  f in Trash
  Trash' = Trash - f
}

pred stutter {
  Trash' = Trash
}

fact init {
  no Trash
}

-- Temporal operators (always/eventually/after/once) are evaluated over a trace.
fact transitions {
  always (stutter or some f: File | delete[f] or restore[f])
}

-- Example trace: at some point Trash is non-empty and next becomes empty (delete -> restore).
example: run { eventually (some Trash and after no Trash) } for 3 but 6 steps

-- Safety property: restore must be preceded by a delete.
assert restoreAfterDelete {
  always (all f: File | restore[f] implies once delete[f])
}
check restoreAfterDelete for 3 but 6 steps

