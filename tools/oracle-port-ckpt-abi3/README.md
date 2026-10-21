# Checkpoint ABI section continuation

A standalone proof crate; no shipped source changes. `generate.py --check`
checks the exact frozen reader excerpt and authentication-prefix excerpt.
The latter is prepared for the symbolic-length stage. Root-specific
receipts, rather than the existence of a harness, determine what passed.

Section roots install four verified field-codec contracts. The functions
implementing those contracts are byte-identical to the pass-2 functions;
the existing successful contract checks are reused, not rerun. The root
wrapper extracts actual private helpers, not a whole linked resume theorem.

`compile.py` uses the prescribed local Lean lock, flags and a private cache.
`run-kani.py` validates the 55 GiB host reservation before a 6G/8G/no-swap/
64-task scope, then executes one explicitly bounded Kani root. A host job
expects verification compilation followed by the named byte/section check,
never finite-field elimination. See the pass-3 STATUS.md for exact limits.

The all-length writer and reader-authentication roots quantify over arbitrary
byte arrays and symbolic prefix lengths up to 57,607 and 1,880 respectively.
Hash argument identity is checked by fat-pointer equality, so the input
content need not be traversed or bounded by the loop unwind. Unwind 70 still
checks every actual writer/reader-prefix loop. Reader field helpers do not
consume either length parameter. This is not a whole-resume certificate.
