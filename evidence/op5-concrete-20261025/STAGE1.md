# Rejected-source mark compatibility

Checked `Op5C_RejectedMarks.source_wrong_split`: literal emitted TX1 rejects
an incorrect split with Rust Parse and only the op16 constant read. Its
batch/query/save site list is empty. Every other operation is universally
quantified and never called; this includes every concrete op5 body.

`first_marks_force_batch` proves the existing FirstMarks premise requires
batch0 in the child log of EVERY op10-tagged event. It checks neither Rust
Ok nor validity of the event in an outer execution.
`no_global_first_mark_association` proves no port can satisfy FirstMarks and
have the source site's empty list on this rejected prefix.

Scope: a checked counterexample to globally faithful source site association
with the current unconditional FirstMarks, not a shipped-source security bug,
not the oracle-inconsistent-read counterexample on an accepted run, and NOT
a refutation of an association restricted to actual successful occurrences.
The rejected source fixture is not the SAME accepted execution in the task.
No accepted execution or row closure is claimed; no new premise is added to
the Op3I theorem. No assumptions of that theorem are discharged.

Final focused target Op5C_RejectedMarks.lean, attempt Op5C_004: exit0,
wall2.157120394986123s, peakRSS5153136KiB,swap0; revision
b14079413c plus dirty new module (full revision/hash in receipt).
All three printed axioms sets are [propext,Classical.choice,Quot.sound].
Attempts001–003 are retained excluded elaboration failures: reserved identifier,
Boolean inequality reduction, and unreduced pure Code return respectively.
No timeout, memory kill, unchanged retry or cap change occurred.
All four used unchanged coherent-host launcher, -j1 -M7000,
6G high/8G max/Swap0/Tasks64; selected dependency hashes in receipts.
Only new prefix module and designated evidence changed. Budget4/80 Lean,
0/40 Kani. No dependency build, package replay, Rust/SBF run or ELF trigger.
