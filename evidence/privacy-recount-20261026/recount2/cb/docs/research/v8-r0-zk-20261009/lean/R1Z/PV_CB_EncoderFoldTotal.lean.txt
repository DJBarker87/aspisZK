import R1Z.PV_CB_EncoderFold
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderFoldTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal

theorem finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b)) (add_total : ∀ a b,Total (inst.add a b))
    (q : Array E 1024#usize) (basis : Array E 512#usize)
    (fuel : Nat) (j : Usize) (p0 p1 : E) (rank : j.val+fuel=512) :
    Total (PV_CB_EncoderFold.finite inst q basis fuel j p0 p1) := by
  induction fuel generalizing j p0 p1 with
  | zero => exact ok_total _
  | succ fuel ih =>
    have more : j<512#usize := by change j.val<512;omega
    have advance := PV_CB_ForwardRange.advance_val j 512#usize more
    unfold PV_CB_EncoderFold.finite
    apply bind_total (PV_CB_EncoderFold.step_total inst mul_total add_total q basis j p0 p1 (by omega))
    intro pair
    exact ih _ pair.1 pair.2 (by omega)

theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (mul_total : ∀ a b,Total (inst.mul a b)) (add_total : ∀ a b,Total (inst.add a b))
    (q : Array E 1024#usize) (basis : Array E 512#usize) (p0 p1 : E) :
    Total (PV_CB_OwnedEncoder.owned.encoder_fold inst q basis 0#usize p0 p1) := by
  rw [PV_CB_EncoderFold.source inst q basis 512 0#usize p0 p1 (by decide)]
  exact finite inst mul_total add_total q basis 512 0#usize p0 p1 (by decide)
#print axioms finite
#print axioms total
end R1Z.PV_CB_EncoderFoldTotal
