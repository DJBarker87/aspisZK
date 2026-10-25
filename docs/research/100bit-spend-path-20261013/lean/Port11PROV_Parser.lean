import Port11PROV_Views
import MultiproofConeParserTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_Parser
open Aeneas Aeneas.Std Result MultiproofConeCanonical

theorem length_wire (proof : Slice U8) (parsed : OraclePortCompactDraft.Parsed)
    (success : OraclePortCompactDraft.parse (bytesOf proof.val)=some parsed) :
    proof.val.length=57607 ∧ parsed.wire=bytesOf proof.val := by
  obtain ⟨header,wire⟩ := OraclePortCompactDraft.parse_header _ _ success
  have len := ((OraclePortHeader.accepts_iff _).mp header).1
  exact ⟨by simpa only [bytesOf,List.length_map] using len,wire⟩

/-- Actual owned reference parser return, including its semantic rows. Its
production adoption at delegated op3/op4 remains a separate producer gate. -/
theorem source (proof : Slice U8) (actual : alloc.vec.Vec (alloc.vec.Vec U8))
    (success : MultiproofParserRef.parser_reference.parse proof=ok (some actual)) :
    ∃ parsed, OraclePortCompactDraft.parse (bytesOf proof.val)=some parsed ∧
      proof.val.length=57607 ∧ parsed.wire=bytesOf proof.val ∧
      MultiproofConeParserControl.decodedRows actual=parsed.semantic ∧
      ∀ b k, b<2 → k<3 → bytesOf (Port11PROV_Views.nodes proof b k).val=
        OraclePortCompactDraft.slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+k))
          (32*OraclePortSelectedDraft.capacity (3*b+k)) := by
  obtain ⟨parsed,parsedOK,wire,rows⟩ := MultiproofConeParserTotal.accepted_parse proof actual success
  have len := (length_wire proof parsed parsedOK).1
  exact ⟨parsed,parsedOK,len,wire,rows,Port11PROV_Views.node_bytes proof len parsed wire⟩

#print axioms length_wire
#print axioms source
end AspisR1.Port11PROV_Parser
end
