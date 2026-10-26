import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_InputDiscovery
open OraclePortStoredDecisionDraftC4

/-- Discovery needs a parsed arithmetic reader as well as the public/late-row
fields. Neither requirement follows from sampler state equality alone. -/
theorem exists_input (p : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix) :
    (∃ i, input p q tr = some i) ↔
      (∃ i, D0InstanceAdmission.Fields tr i) ∧
      (∃ d, LiteralMatchingData.read (typedRows p q tr) = some d) := by
  constructor
  · rintro ⟨i,h⟩
    have fields := input_fields p q tr i h
    exact ⟨⟨i,fields.1⟩,⟨i.data,fields.2⟩⟩
  · rintro ⟨fields,⟨d,read⟩⟩
    unfold input
    rw [dif_pos fields,read]
    exact ⟨_,rfl⟩

#print axioms exists_input
end AspisR1.F3L_InputDiscovery
end
