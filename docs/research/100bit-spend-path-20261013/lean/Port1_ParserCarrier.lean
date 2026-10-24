import Port1_StoredCarrier
import MultiproofConeParserTotal

/-! Bind the canonical logical proof to the actual owned parser cone result.
Production adoption/lowering of that cone remains its existing boundary. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_ParserCarrier
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft Port1_StoredCarrier MultiproofConeCanonical

/-- A successful actual parser result determines the canonical logical proof;
there is no separately chosen semantic row list. -/
theorem source_parse (s : Submission) (stored : Slice U8)
    (same : bytesOf stored.val = s.stored)
    (actual : alloc.vec.Vec (alloc.vec.Vec U8))
    (accepted : MultiproofParserRef.parser_reference.parse stored = .ok (some actual)) :
    ∃ p, parse s.stored = some p ∧ p.wire = s.stored ∧
      MultiproofConeParserControl.decodedRows actual = p.semantic ∧
      (input s).proof = parsedProof p := by
  obtain ⟨p,parsed,wire,rows⟩ := MultiproofConeParserTotal.accepted_parse stored actual accepted
  rw [same] at parsed wire
  exact ⟨p,parsed,wire,rows,parsed_proof s p parsed⟩

#print axioms source_parse
end AspisR1.Port1_ParserCarrier
end
