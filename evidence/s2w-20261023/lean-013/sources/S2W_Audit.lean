import S2W_OracleAudit
import S2W_SnapshotJoin

/-! One focused final import-union axioms audit. This is not a native execution
certificate, S2CallerFacts constructor, or frozen release replay. -/
#print axioms AspisR1.S2W.OracleAudit.mask_runtime
#print axioms AspisR1.S2W.OracleAudit.mask_observed
#print axioms AspisR1.S2W.OracleAudit.bound_runtime_not_total
#print axioms AspisR1.S2W.Snapshot.snapshot
#print axioms AspisR1.S2W.Snapshot.to_vec_identity
#print axioms AspisR1.S2W.Snapshot.admitted_snapshot
#print axioms AspisR1.S2W.Snapshot.rejected_length
#print axioms AspisR1.S2W.Snapshot.borrow_error
#print axioms AspisR1.S2W.Snapshot.successful_shape
#print axioms AspisR1.S2W.Snapshot.checkpoint_entry_size
#print axioms AspisR1.S2W.SnapshotJoin.data_success
#print axioms AspisR1.S2W.SnapshotJoin.snapshot_shape
#print axioms AspisR1.S2W.SnapshotJoin.accepted_checkpoint_length
