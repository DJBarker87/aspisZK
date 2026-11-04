# Reached copy lengths

The mandated AccountMeta calculation is 6 × 34 = 204, then unwind205.
The same frozen invocation body also initializes seven AccountInfo entries
and inserts the verifier checkpoint. Their host layout is 48 bytes each:
four 8-byte references/handles, one 8-byte epoch, three bools, and five bytes
of alignment padding. Its reallocation preserves 7 × 48 = 336 bytes.
Consequently the completed combined-call bound is max(204,336)+1 = 337.
NFV_K001 demonstrates the insufficiency of205 at the KMX realloc loop.
This is an unwind bound correction, not a solver-time or memory-cap increase.
No timed-out source is resubmitted unchanged; observations are split by index
and key byte. All such verdicts remain inconclusive until terminal receipts.
