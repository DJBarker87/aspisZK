import JGb_MaskedArithmetic
import JFu_MaskTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_MaskedNonvacuity
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues
open JFu_MaskInputs
/-- Honest retained-mask execution plus actual masked arithmetic. The terminal
operand is explicit; no equality to the retained final running value is claimed. -/
theorem source (terminal : MQ) (ht : Canon terminal) :
    ∃ mask out,FIp_SemanticArithmetic.mask c1 maskOnly g point=ok mask ∧ Canon mask ∧
      JGb_MaskedArithmetic.run terminal mask=ok out ∧ Canon out ∧
      decode out=decode mask+decode JFm_Begin.challenges.eta*decode terminal+
        decode JFu_ClaimsData.q115 := by
  obtain ⟨mask,hm,hmc⟩ := JFu_MaskTotal.source
  obtain ⟨out,ho,hoc,hov⟩ := JGb_MaskedArithmetic.source terminal mask ht hmc
  exact ⟨mask,out,hm,hmc,ho,hoc,hov⟩
#print axioms source
end AspisR1.JGb_MaskedNonvacuity
end
