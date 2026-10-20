# Actual-crate stage-2 extraction attempt

VERIFIER SOURCE CHANGE. Runtime-gated refactor revision: `7d4c136f0`.

`inventory.py` records 78 source declaration spans, including the account
adapter as a source pin. `run.py` starts Charon at the actual crate's
`verifier::candidate::tx2_authenticated`, preserving every orchestration body.
The adapter's SDK/account wrapper is outside that root. Arithmetic, allocation,
hash, weights, domain and trace frontiers are explicit in the input pins.
Tools are the stage-1 Charon/driver/extended-static Aeneas hashes, checked
before either phase; each phase uses a fresh 6G/8G/swap0/Tasks64 scope and
receipts. Runs are optimized; no proof generation or finite-field elimination
is performed. One compiler job is used for Charon, as in the stage-1 packets.

Charon succeeded and emitted valid LLBC. Aeneas failed on the post-finish
Accumulator shared borrow at candidate.rs:237. The move/reconstruction change
is not sufficient for this pinned translator. Per the stop-on-failure mandate,
no further attempt, source edit or first-fact proof was made. No Lean output
was emitted. The report and manifest retain exact input/tool/LLBC hashes,
commands, exits, timing, RSS and swaps. No binary or LLBC file is committed.

These are retained failed commands, not instructions to rerun unchanged.
The receipt wrapper refuses an existing run directory. A future attempt needs
a specifically changed source or translation boundary and new run names.
