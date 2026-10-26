import R1Z.PV_CB_EncoderBasis
import R1Z.PV_CB_EncoderFoldTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal

theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (zero_total : Total inst.ZERO) (one_total : Total inst.ONE)
    (mul_total : ∀ a b,Total (inst.mul a b))
    (add_total : ∀ a b,Total (inst.add a b))
    (sub_total : ∀ a b,Total (inst.sub a b))
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    Total (PV_CB_OwnedEncoder.owned.encoder inst q p) := by
  unfold PV_CB_OwnedEncoder.owned.encoder
  apply bind_total (PV_CB_EncoderBasis.total inst one_total mul_total add_total sub_total p.x)
  intro basis
  apply bind_total zero_total;intro z
  apply bind_total (PV_CB_EncoderFoldTotal.total inst mul_total add_total q basis z z)
  intro pair
  apply bind_total (mul_total p.y pair.2);intro y
  exact add_total pair.1 y
#print axioms total
end R1Z.PV_CB_EncoderTotal
