import PV_B3_CanonicalSource
import PV_B3_FieldScalar
import R1Z.ProverRwP7CurrentBaseBridge
import R1Z.ProverCommitM31Ops48
noncomputable section
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result
set_option autoImplicit false
 theorem current_reduce (x : U64) : ∃ z, S.reduce x = ok z ∧ M z := by
  have eq : S.reduce x = R1Z.ProverRwP7CurrentBaseBridge.S.reduce x := by
    with_unfolding_all rfl
  rw [eq,R1Z.ProverRwP7CurrentBaseBridge.reduce]
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x = ok z := by
    rw [R1Z.ProverCommitPrimitive47.reduce,hz]
  exact ⟨z,R1Z.ProverCommitRelease47.reduce x z checked,hc⟩
#print axioms current_reduce
end PV_B3_Canonical
