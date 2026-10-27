import FJl_PackedSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PackedInjective
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
/-- Distinct queried leaf indices remove first-occurrence ambiguity without
assuming anything about the hash oracle. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat)
    (unique : Function.Injective (fun j : Fin 22=>index q kind j.val)) (j : Fin 22) :
    packed parsed q kind (index q kind j.val)=some (OraclePortPackedChoiceC4.payload parsed kind j.val) := by
  obtain ⟨first,hfirst⟩ := OraclePortPackedChoiceC4.position_exists q kind j.val j.isLt
  obtain ⟨bound,same⟩ := OraclePortPackedChoiceC4.position_fields q kind _ first hfirst
  have equal : (⟨first,bound⟩ : Fin 22)=j := unique same
  have at := FJl_PackedSelected.value parsed q kind _ first hfirst
  simpa only [congrArg Fin.val equal] using at
#print axioms value
end AspisR1.FJl_PackedInjective
end
