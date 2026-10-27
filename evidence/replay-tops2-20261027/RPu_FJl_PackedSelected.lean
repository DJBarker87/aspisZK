import Port5Q1_Parsed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_PackedSelected
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
/-- At its selected first occurrence, packed bytes need no recovery law. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144) (kind leaf pos : Nat)
    (first : selectedPosition q kind leaf=some pos) :
    packed parsed q kind leaf=some (OraclePortPackedChoiceC4.payload parsed kind pos) := by
  simp only [packed,first,Option.map_some,OraclePortPackedChoiceC4.payload]
#print axioms value
end AspisR1.FJl_PackedSelected
end
