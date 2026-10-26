import RPz7_AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Map
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft OraclePortSelectedDraft

/-- One indexed map supplies every occurrence, including equal parents on
opposite sides of the TX1/TX2 split. No per-batch recovery function is chosen. -/
 theorem occurrences (p : Parsed) (q : Fin 22 → Fin 262144) (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos < 22 → recovered (index q 2 pos) =
      some (OraclePortPackedChoiceC4.payload p 2 pos)) :
    (∀ pos, pos < 22 → OraclePortStoredDecisionDraftC4.packed p q 2 (index q 2 pos) =
      recovered (index q 2 pos)) ∧
    (∀ left right, left < 22 → right < 22 → index q 2 left = index q 2 right →
      OraclePortPackedChoiceC4.payload p 2 left = OraclePortPackedChoiceC4.payload p 2 right) :=
  ⟨fun pos bound => OraclePortPackedChoiceC4.packed_agrees p q 2 recovered authenticated pos bound,
    fun left right hl hr same => OraclePortPackedChoiceC4.repeated_payloads p q 2 recovered authenticated left right hl hr same⟩

#print axioms occurrences
end AspisR1.AuS1_Map
end
