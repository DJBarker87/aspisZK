import NMT_345CanonicalCommon
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
open NFY_NBG_PaymentChecks NFY_NBG_PaymentValidators

theorem withdrawal_canonical (p : W) (good : withdrawal p = .Ok ()) :
 canonical p.anchor_root = true ∧ canonical p.nullifier = true ∧
 canonical p.change_commitment = true := by
 unfold withdrawal at good
 cases hc : common (wc p) with
 | Err e => simp only [hc] at good; cases good
 | Ok u =>
  cases u
  have fields := payment_common_canonical (wc p) hc
  simp only [hc] at good
  refine ⟨fields.1,fields.2,?_⟩
  split at good
  · cases good
  · split at good
    · cases good
    · cases hz : canonical p.change_commitment <;> simp_all
#print axioms withdrawal_canonical
end NMT_345
