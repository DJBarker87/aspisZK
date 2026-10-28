import R1Z.PV_RDB1_CombinedAudit

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_ClosureReplay
/-- Focused replay, universally quantified over the restored generic row. -/
theorem every_restored_row :
    ∀ T : Type, PV_RDB1_V186.defaultCall (ok (alloc.vec.Vec.new T)) =
      ok (alloc.vec.Vec.new T) ∧ (alloc.vec.Vec.new T).val = [] :=
  fun T => PV_RDB1_CombinedAudit.restored_row T
#print axioms every_restored_row
end R1Z.PV_RDB1_ClosureReplay
