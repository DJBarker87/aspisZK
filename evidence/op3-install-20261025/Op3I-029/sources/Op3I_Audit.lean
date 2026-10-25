import Op3I_Accepted
import Op3I_Witness
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op3I_Audit
open AspisR1CurrentCaller

/-- Expand every frozen2 header field checked by a successful source op3.
This has no whole-parser success or scan/transcript hypothesis. -/
theorem header_fields (proof : Slice U8) (v : transport.Variant)
    (call : Op3I_Install.sourceBody proof = ok (.Ok v)) :
    let b := MultiproofConeCanonical.bytesOf proof.val
    v = .S2 ∧ b.length = 57607 ∧ b.take 8 = OraclePortHeader.magic ∧
      b[8]? = some 2 ∧ (b.drop 9).take 7 = List.replicate 7 0 := by
  obtain ⟨hv,header⟩ := Op3I_Install.header_of_success proof v call
  exact ⟨hv,(OraclePortHeader.accepts_iff _).mp header⟩

/-- Any failed source header condition excludes a successful source return.
Actual Err/outer failure order remains the extracted body's control flow. -/
theorem rejects_malformed_header (proof : Slice U8)
    (bad : let b := MultiproofConeCanonical.bytesOf proof.val
      b.length ≠ 57607 ∨ b.take 8 ≠ OraclePortHeader.magic ∨
      b[8]? ≠ some 2 ∨ (b.drop 9).take 7 ≠ List.replicate 7 0)
    (v : transport.Variant) :
    Op3I_Install.sourceBody proof ≠ ok (.Ok v) := by
  intro call
  obtain ⟨_,len,magic,tag,tail⟩ := header_fields proof v call
  rcases bad with bad | bad | bad | bad
  · exact bad len
  · exact bad magic
  · exact bad tag
  · exact bad tail

#print axioms header_fields
#print axioms rejects_malformed_header
#print axioms Op3I_Accepted.accepted_pair_claims_op3
#print axioms Op3I_Cuts.full_parse_of_remaining
#print axioms Op3I_Nonvacuity.extraction_satisfiable
#print axioms Op3I_Witness.source_success
end AspisR1.Op3I_Audit
end
