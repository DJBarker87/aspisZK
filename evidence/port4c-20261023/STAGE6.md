# Whole native geometry gather

`Port4C_GeometryLoop.accepted` derives the successful terminal call on its
actual final raw/line_z buffers by symbolic induction. Its final raw buffer
has exactly five entries per visited query and every entry passed the actual
zero test. `Port4C_GeometryFields.accepted` derives selected slice contents,
start, line_z length, flat length, nonzero raw words and the SAME terminal
inversion/grouping call from the accepted complete constructor. `both_sizes`
proves the actual starts0/10 and line_z lengths10/12; the raw inversion
inputs therefore have lengths50/60. No pre-supplied length/nonzero/independent
terminal observation is used.

Closed: gather/control/range/sizing/raw-zero tests. Open: native prefix,
backward inverse and collect/std lowering to the proved reciprocal/group
semantics; raw nonzero to field nonzero needs domain canonicality. The latter
must not be silently inferred for arbitrary noncanonical M31 words.

Accepted final035/037/040, all exit0, swap0, standard axioms only. Full exact
section6 fields are in receipts. Intermediate033 was green before adding
the terminal-not-continue lemma. Failed036 is an excluded tuple-elaboration
attempt. No cap increase, memory kill, timeout or full manifest. Budget40/100
at the geometry fields target,0/60 Kani; row attempts are interleaved.
No shipped source, ELF, other worktree or key changed.
