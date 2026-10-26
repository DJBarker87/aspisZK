# Repaired import-context recovery

Attempts 30800–30811 compile all twelve previous missing-object failures successfully. Each source SHA is unchanged; the physical namespace context was repaired in the prior job. No timeout or memory failure was retried. Subsequent dependency-ordered work continues in one scope at a time. Per-attempt exact commands, source/blob revisions, dependency fingerprints, exit, wall, RSS, swaps and full printed-axioms output are in EJS_attempts.jsonl and receipts/. All first 70 compiler and printed-axiom gates pass; peak RSS 4,137,244 KiB, swaps zero.

This is cache recovery only: no actual top premise removed, no new security non-vacuity claim, no shipped source change or ELF rebuild trigger.
