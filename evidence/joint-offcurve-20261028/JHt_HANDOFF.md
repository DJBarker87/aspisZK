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

Stage 2: bounded structural modPow correctness, Lucas certificate bridge and
255-bit preflight passed (JHt_006 and JHt_008). `JHt_Prime` proves
2^255-19 prime with 53 Pratt nodes and separate checked residue theorems.
JHt_011: exit 0, 5.806709420 seconds, peak 3384368 KiB, swap 0. Standard axioms only.
Generator --check passes. Rejected earlier attempts are retained.
JHt_003 corrected an own LEAN_PATH ordering error: complete pinned Mathlib
precedes a partial same-version overlay; compared ModEq object hashes match.
JHt_004/005: well-founded executable would not reduce through tactics.
Replaced concrete computation with structural bit budget (JHt_006); original
symbolic theorem remains valid but unused by final arithmetic. JHt_007 hit
elaborator recursion depth; kernel evaluator JHt_008 passes without raising
limits. JHt_009 had a cast rewrite mismatch, JHt_010 accidental elaborator
unfolding. JHt_011 uses local irreducibility to keep rewrites symbolic and
`decide +kernel` only for one bounded exponentiation at a time.
11/30 Lean attempts used. Seven fixture facts still open.
