import R1Z.PV_Canon_Reduce
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
theorem current_mul (x y : U32) : ∃ z, S.mul x y = .ok z ∧ M z := by
  change ∃ z, ProverRwP7CurrentBaseBridge.S.mul x y = .ok z ∧ M z
  rw [ProverRwP7CurrentBaseBridge.mul]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.mul_exact x y
  exact ⟨z,hz,hc⟩
#print axioms current_mul
end R1Z.PV_Canon
