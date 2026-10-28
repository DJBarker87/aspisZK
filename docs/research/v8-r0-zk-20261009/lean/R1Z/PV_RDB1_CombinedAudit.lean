import R1Z.PV_RDB1_V186

open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_CombinedAudit
/-- The sole restored row retains exactly its existing Result/value equation. -/
theorem restored_row (T : Type) :
    PV_RDB1_V186.defaultCall (ok (alloc.vec.Vec.new T)) =
    ok (alloc.vec.Vec.new T) ∧ (alloc.vec.Vec.new T).val = [] :=
  ⟨PV_RDB1_V186.selected_result T, PV_RDB1_V186.constructor_value T⟩
#print axioms restored_row
#print axioms PV_RDB1_V186.empty_from_zero_length
#print axioms PV_RDB1_V186.constructor_value
#print axioms PV_RDB1_V186.complete
#print axioms PV_RDB1_V186.selected_result
end R1Z.PV_RDB1_CombinedAudit
