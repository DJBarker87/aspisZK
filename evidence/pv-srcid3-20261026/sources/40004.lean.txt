import R1Z.PV_Src_WithdrawalRecipient

/-! Canonical withdrawal normalization changes only unused recipient fields,
retaining the original public input and every semantic admission condition. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalNormalize
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

def normalize (i : BuilderCanonical.Instance (K := K)) : BuilderCanonical.Instance (K := K) :=
  if hv : i.val.1.variant = .withdrawal then
    ⟨(i.val.1,PV_Src_WithdrawalRecipient.erase i.val.2),by
      rw [PV_Src_WithdrawalRecipient.lift_erase]
      exact PV_Src_WithdrawalRecipient.preserves _ _ hv i.property⟩
  else i

theorem public_eq (i : BuilderCanonical.Instance (K := K)) :
    (normalize i).val.1 = i.val.1 := by unfold normalize; split <;> rfl

theorem transfer (i : BuilderCanonical.Instance (K := K))
    (hv : i.val.1.variant = .privateTransfer) : (normalize i).val.2 = i.val.2 := by
  simp only [normalize,hv,reduceCtorEq,↓reduceDIte]

theorem withdrawal (i : BuilderCanonical.Instance (K := K))
    (hv : i.val.1.variant = .withdrawal) :
    (normalize i).val.2 = PV_Src_WithdrawalRecipient.erase i.val.2 := by
  simp only [normalize,hv,↓reduceDIte]

#print axioms public_eq
#print axioms transfer
#print axioms withdrawal
end R1Z.PV_Src_CanonicalNormalize
