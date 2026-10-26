# Ordered reference copy continuation

PoolU_Step proves success inversion and exact source-prefix propagation for
program errors, interpreter failures and divergence, returning the prefix's
state rather than rolling it back or replacing it. State may include all effects.
PoolU_CopyTail.accepted composes the two-copy continuation with the SAME returned
images and post-prefix store. It derives checkpoint/master bytes, all metadata
and other-physical-key frames. rejected_prefix keeps the exact error and state.

This is a reference composition, not construction of the native P1 prefix.
Its `prelude` parameter is explicit and unconstrained; the theorem neither
supplies a native/source equality nor proves canonical commit association.
It removes no global premise and is not accepted_p1_writes_copy.

Attempts001/003 passed;002 failed on reserved identifier `prefix`, corrected
in003 (changed source). No timeout/memory kill. All six new theorem audits
are standard-only. Exact target/hash/deps/revision/exit/wall/RSS/swap/axioms and
failed source snapshot are in each PoolU_NNN receipt. Kani0; Lean3/100.
