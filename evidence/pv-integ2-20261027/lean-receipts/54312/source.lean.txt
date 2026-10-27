import R1Z.PV_CB_EncoderRound
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderBasis
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal

theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (one_total : Total inst.ONE)
    (mul_total : ∀ a b,Total (inst.mul a b))
    (add_total : ∀ a b,Total (inst.add a b))
    (sub_total : ∀ a b,Total (inst.sub a b)) (x : E) :
    Total (PV_CB_OwnedEncoder.owned.basis inst x) := by
  unfold PV_CB_OwnedEncoder.owned.basis
  apply bind_total one_total
  intro one
  exact PV_CB_EncoderRound.total inst one_total mul_total add_total sub_total
    9 1#usize x (Array.repeat 512#usize one) (by decide) (by decide)
#print axioms total
end R1Z.PV_CB_EncoderBasis
