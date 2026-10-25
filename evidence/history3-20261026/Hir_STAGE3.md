# Hir stage 3: selected causal writer and actual suffix

Target not yet established; zero global ledger rows removed.

Hir_SelectedOrigin.causal_writer derives a reached successful native TX1 for
the separate verifier checkpoint selected by an accepted native TX2. It uses
source-derived TX2 owner and marker checks; genesis excludes preexisting
initialized verifier-owned cells; admissible records Solana's zero-data owner-
assignment rule. These runtime conditions are explicit. In particular the old
unrestricted foreign projection does NOT establish genesis provenance.

Hir_BirthSuffix.suffix extracts the ACTUAL post-writer event suffix of the same
schedule, classified from source checks. Hir_LifetimeVersion.causal_pair derives
shared first/second SourceCuts and a CheckpointVersionBinding between the actual
native post-copy payload and the selected checkpoint, using that suffix. No
separately supplied sameKey, load2, accepted TX1, source cut or history is needed
in this constructed lifetime family. No independently chosen TX1 is identified
with the selected causal writer. This is model/source-family progress, not a
recount removal in T2R_Top.deployed; runtime/Pool completeness is unproved.

Hir_RecordErasure.exact establishes recording's exact all-world result/log
erasure. Hir_RecordNative.result identifies the recorded reached call list with
that native schedule. Hir_WriterSelect/Hir_SelectOne begin a deterministic pure
selector over those observations, with no H argument. It does not yet close
the selected experiment's complete probability/source transport.

All current new modules have successful exact-source receipts.52/100 Lean
submissions,3/30 Kani. Failed development versions remain in their receipts;
only passing standard-axiom results are accepted. No timeout or memory kill,
cap/heartbeat/depth change, package replay, shipped source change or tool repair.

Still open: complete Pool create/write/read/close/authority/owner dispatcher
instance; real runtime lifetime/scheduler/initial-state association; selected
writer's single account collision experiment and actual T2R continuation.
L159 is excluded. The existing2965 single-loss/margin results are inherited,
not yet a deployed release result. No shipped-source security counterexample.
