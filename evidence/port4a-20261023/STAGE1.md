# Stage 1: same-prefix ten-call provenance

`Port4A_Prefix.reached_calls` in the soundness lean directory derives, from
ONE `WriterPrefix (Port3_NativeWriterShape.installed ...)`, existential witnesses
for its actual initial/pending/returned/g/geometry cuts. It proves initial
next0, initial terms synchronization, exactly ten ordered successful calls to
CURRENT native query parent (release trace and S7 owned-push adapter), final
pending terms10 and exact writer rhs/power/next equality to that returned state.
No independently successful run or model/provenance premise is introduced.

Lean002 passed, exit0, wall4.111330304s, peak4417092KiB, swaps0, only
propext/Classical.choice/Quot.sound. Lean001 was an excluded elaboration failure
(missing explicit existential pair type), corrected before retry. Exact revision,
command, source/dependency hashes and axioms in per-attempt receipts.

This discharges the prefix-level term/call-control gap, not field/model meaning.
Prepared canonicality, rhs/power canonicality, ten-step frozen2 arithmetic,
native push/std ABI and writer adoption remain open. Reused Port3 dependency
objects are directly pinned in receipts; no frozen manifest replay was run.
Shipped source unchanged; no ELF rebuild or fresh binary claim.
