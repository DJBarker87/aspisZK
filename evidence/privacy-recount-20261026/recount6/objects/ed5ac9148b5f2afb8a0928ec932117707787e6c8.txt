import R1Z.PV_CB_Op229Transport
set_option autoImplicit false
namespace R1Z.PV_CB_Op229Codec
open ProverRwFull PV_CB_Op229Transport
theorem after_roundtrip (x : After) : unafter (after x) = x := by cases x; rfl
theorem source_after_roundtrip (x : SourceAfter) : after (unafter x) = x := by cases x; rfl
theorem snapshot_roundtrip (x : Snap) : unsnapshot (snapshot x) = x := by cases x; rfl
theorem source_snapshot_roundtrip (x : SourceSnap) : snapshot (unsnapshot x) = x := by cases x; rfl
theorem roundtrip (base : ExternalTypes) (x : Late base) : decode base (encode base x) = x := by
  letI : ExternalTypes := native base
  cases x
  rfl
theorem source_roundtrip (base : ExternalTypes) (x : SourceLate) : encode base (decode base x) = x := by
  letI : ExternalTypes := native base
  cases x
  rfl
#print axioms after_roundtrip
#print axioms source_after_roundtrip
#print axioms snapshot_roundtrip
#print axioms source_snapshot_roundtrip
#print axioms roundtrip
#print axioms source_roundtrip
end R1Z.PV_CB_Op229Codec
