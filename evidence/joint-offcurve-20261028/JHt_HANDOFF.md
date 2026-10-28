# Off-curve proof work

Stage 1: `JHt_ModPow.correct` proves binary modular exponentiation equals
`Nat.pow` modulo m, for arbitrary Nat inputs. One recursive occurrence per
exponent bit; bases reduced after each square. No huge ordinary power is
computed. Check JHt_002: exit 0, 1.507738701 seconds, peak 3,323,124 KiB,
swap 0; axioms propext and Quot.sound. JHt_001 was a rejected rewrite proof
(exit 1, 1.460076083 seconds, peak 3,307,412 KiB, swap 0); corrected before
retry. Exact revision, source hashes, commands and caps are in each receipt.

Own host cache was seeded by copying the assigned JHs cache (345 MiB).
Seed was read only; own cache retained. All scopes 6G/8G, swap 0, TasksMax64,
Lean -M7000. 2/30 Lean attempts used. Seven fixture facts remain open.
