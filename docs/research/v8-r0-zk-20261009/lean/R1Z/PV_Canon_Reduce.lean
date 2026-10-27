import R1Z.PV_Canon_Carrier
import R1Z.ProverRwP7CurrentBaseBridge
import R1Z.ProverCommitM31Ops48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
namespace S
abbrev reduce := ProverRwP7CurrentFieldSource.aspis_core.field.reduce_u64
abbrev mul := ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev add := ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev sub := ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
end S
theorem current_reduce (x : U64) : ∃ z, S.reduce x = .ok z ∧ M z := by
  change ∃ z, ProverRwP7CurrentBaseBridge.S.reduce x = .ok z ∧ M z
  rw [ProverRwP7CurrentBaseBridge.reduce]
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  have checked : AspisR1ProducerChecked47.field.reduce_u64 x = .ok z := by
    rw [ProverCommitPrimitive47.reduce,hz]
  exact ⟨z,ProverCommitRelease47.reduce x z checked,hc⟩
#print axioms current_reduce
end R1Z.PV_Canon
