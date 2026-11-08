import NNV_PrepareFrontCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareFilled
open RSL NNH_Libraries

theorem returned (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) :
 env.reservation = true ∧ p.logical = List.replicate (LOGICAL_SEMANTIC+LOGICAL_Y1) (0 : UInt8) := by
 have called := p.filled
 change (if env.reservation then .ok (List.replicate (LOGICAL_SEMANTIC+LOGICAL_Y1) (0 : UInt8)) else Except.error ()) = .ok p.logical at called
 cases h : env.reservation with
 | false => rw [h] at called; cases called
 | true =>
  rw [h] at called
  exact ⟨rfl,(Except.ok.inj called).symm⟩
#print axioms returned
end AspisR1.NNV_PrepareFilled
end
