# R144: complete source serializer proof

The actual R136 `bytes` function returns the four U32 limbs of every QM31
value as 16 little-endian bytes, in source order. The theorem is generic in
the input slice and assumes only that its allocated byte length fits usize.
The 358-value specialization uses the same theorem; no concrete field values
or long recurrence are evaluated.

The source iterator and buffer invariant is proved one step at a time. The
final source result equals the exact encoded vector, not merely its length.
The focused leaf `AspisV8R19/R144BeforeOodBytesBridge` compiled successfully
in 6.14 seconds with 2,593,176 KiB peak process RSS and zero swap. All nine
printed theorem audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The exact source revision, source digest, command, cap, and
complete audits are retained in `evidence/r144-before-ood-bytes`.

The next proposition is the full `before_ood` execution and failure/state
composition. Later query sampling, full published-view privacy, and soundness
are still open. No verifier source, security parameter, or CU evidence changed;
the existing verifier results remain 999,790 / 999,532 CU.
