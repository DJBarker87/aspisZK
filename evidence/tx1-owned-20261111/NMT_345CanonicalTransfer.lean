import NMT_345CanonicalCommon
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
open NFY_NBG_PaymentChecks NFY_NBG_PaymentValidators
/-- Exact payment-field invariant on the returning validator arm. This is
an INTERNAL step lemma; parent roots never assume a child's success. -/
theorem transfer_canonical (p : T) (good : transfer p = .Ok ()) :
 canonical p.anchor_root = true ∧ canonical p.nullifier = true ∧
 canonical p.recipient_commitment = true ∧ canonical p.change_commitment = true := by
 unfold transfer at good
 cases hc : common (tc p) with
 | Err e => simp only [hc] at good; cases good
 | Ok u =>
  cases u
  have fields := payment_common_canonical (tc p) hc
  simp only [hc] at good
  refine ⟨fields.1,fields.2,?_⟩
  cases hr : canonical p.recipient_commitment <;> cases hz : canonical p.change_commitment <;>
   simp_all
#print axioms transfer_canonical
end NMT_345
