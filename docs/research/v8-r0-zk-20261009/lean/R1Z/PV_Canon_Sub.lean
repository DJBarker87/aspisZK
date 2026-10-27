import R1Z.PV_Canon_Reduce
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
theorem current_sub (x y : U32) (hx : M x) (hy : M y) : ∃ z, S.sub x y = .ok z ∧ M z := by
  change ∃ z, ProverRwP7CurrentBaseBridge.S.sub x y = .ok z ∧ M z
  rw [ProverRwP7CurrentBaseBridge.sub]
  obtain ⟨z,hz,hc,_⟩ := ProverCommitM31Ops48.sub_exact x y hx hy
  exact ⟨z,hz,hc⟩
#print axioms current_sub
end R1Z.PV_Canon
