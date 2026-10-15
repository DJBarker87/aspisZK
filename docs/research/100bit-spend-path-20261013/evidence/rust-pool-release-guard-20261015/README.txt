G_R1.7 source guard proposal. Only exact [3,10], [3,11], and ASQ8-prefixed
inputs reach the Pool adapter. All other data rejects before accounts.
Lifecycle 4/5/6 writes proof/public buffers in existing helper code, so it
is rejected rather than asserted harmless. Release provisioning through the
old lifecycle entrypoints must be reconciled before deployment.

Native tests: conflicting proof borrow + unchanged checkpoint (1 passed);
route predicate including every zero/one/two-byte input (2 passed).
All checks exit 0, zero swaps; exact times/RSS/source pins are adjacent.
The prior SBF artifact/replay is not evidence for this changed source.
