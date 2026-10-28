import R1Z.PV_Join_OwnedCtBridge5
import R1Z.PV_Join_Canonical5
import R1Z.ProverCommitM31Ops48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_ReducerCanonical5
open Aeneas Aeneas.Std Result PV_Join_Canonical5

theorem release (x : U64) :
    ∃ z : U32, AspisR1ProducerRelease47.field.reduce_u64 x = .ok z ∧ M z := by
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x = .ok z := by
    rw [ProverCommitPrimitive47.reduce,hz]
  exact ⟨z,ProverCommitRelease47.reduce x z checked,hc⟩

theorem extracted (x : U64) :
    ∃ z : U32, PV_Join_Direct5Source.aspis_core.field.ct.reduce64 x = .ok z ∧ M z := by
  change ∃ z : U32, PV_Join_OwnedCtBridge5.S.reduce x = .ok z ∧ M z
  rw [PV_Join_OwnedCtBridge5.reduce]
  exact release x

#print axioms release
#print axioms extracted
end R1Z.PV_Join_ReducerCanonical5
