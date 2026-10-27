import JGd_MaskSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_MaskedGate
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic FIp_SemanticValues
open JGd_NumericData
attribute [local irreducible] HMul.hMul HAdd.hAdd

/-- Numeric operand required at the actual gate. This does not identify the
public terminal call's return with this operand. -/
theorem formula : decode mask + decode JFm_Begin.challenges.eta * decode neededTerminal +
    decode JFu_ClaimsData.q115 = decode running := by
  change JGd_ExactWords.value maskWords +
    JGd_ExactWords.value ((1518895880,1177859893),(464691262,913595700)) *
      JGd_ExactWords.value neededWords +
        JGd_ExactWords.value ((29830584,496441005),(563440420,1626102052)) = decode running
  dsimp only [maskWords,neededWords]
  rw [terminal_product,partial_value,running_value]
  rfl
#print axioms formula

theorem source : JGb_MaskedArithmetic.run neededTerminal mask = ok running := by
  obtain ⟨out,call,hc,hv⟩ := JGb_MaskedArithmetic.source neededTerminal mask
    neededTerminal_canonical mask_canonical
  have same := JGd_MainInjective.source out running hc running_canonical (hv.trans formula)
  exact same ▸ call
#print axioms source

theorem retained : ∃ actualMask,
    FIp_SemanticArithmetic.mask JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly
      JFu_MaskInputs.g JFu_MaskInputs.point = ok actualMask ∧ Canon actualMask ∧
    JGb_MaskedArithmetic.run neededTerminal actualMask = ok running :=
  ⟨mask,JGd_MaskSource.source,mask_canonical,source⟩
#print axioms retained
end AspisR1.JGd_MaskedGate
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_TerminalCriterion
open Aeneas Aeneas.Std Result FIp_SemanticArithmetic FIp_SemanticValues
open JGd_NumericData

theorem eta_nonzero : decode JFm_Begin.challenges.eta ≠ 0 := by
  intro h
  have h0 := congrArg (fun q => q.re.re) h
  change (1518895880 : ZMod 2147483647)=0 at h0
  norm_num at h0
#print axioms eta_nonzero

/-- The actual arithmetic gate accepts exactly one canonical terminal
operand. Establishing the public terminal return is still a separate source
obligation, not an existence claim hidden in this equivalence. -/
theorem source (terminal : MQ) (ht : Canon terminal) :
    JGb_MaskedArithmetic.run terminal mask = ok running ↔ terminal = neededTerminal := by
  constructor
  · intro call
    obtain ⟨out,called,hc,hv⟩ := JGb_MaskedArithmetic.source terminal mask ht mask_canonical
    have same : out=running := Result.ok.inj (called.symm.trans call)
    subst out
    have valueEq : decode JFm_Begin.challenges.eta * decode terminal =
        decode JFm_Begin.challenges.eta * decode neededTerminal := by
      apply add_left_cancel (a:=decode mask)
      apply add_right_cancel (a:=decode JFu_ClaimsData.q115)
      exact hv.symm.trans JGd_MaskedGate.formula.symm
    exact JGd_MainInjective.source terminal neededTerminal ht neededTerminal_canonical
      (mul_left_cancel₀ eta_nonzero valueEq)
  · intro same
    subst terminal
    exact JGd_MaskedGate.source
#print axioms source
end AspisR1.JGd_TerminalCriterion
end
