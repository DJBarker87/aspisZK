import NJM_ChildDomain
set_option autoImplicit false
namespace AspisR1.NJM_SemanticDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Original semantic source returns only Ok or RowOrder on its actual
round-row domain. Hash failure/divergence is outer and remains observable. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H)
 (record : r1_wire.ValidatedRecord) (bound : record.row.val≤24) :
 NJM_ChildDomain.Good (r1_wire.SemanticTranscript.semantic_validated D t record) := by
 have notInvalid : ¬ record.row>24#u8 := by scalar_tac
 simp only [r1_wire.SemanticTranscript.semantic_validated,r1_wire.ValidatedRecord.impl.row,
  r1_wire.ValidatedRecord.impl.framed,bind_tc_ok,if_neg notInvalid]
 have good:=NJM_ChildDomain.block D t record.row record.framed
 generalize call : r1_wire.SemanticTranscript.sample_block_validated D t record.row record.framed=reply at good ⊢
 cases reply with
 | fail error => trivial
 | div => trivial
 | ok pair =>
   rcases pair with ⟨inner,after⟩
   cases inner with
   | Err error => cases error <;> exact good
   | Ok block =>
     change NJM_ChildDomain.Good (do
      let q ← AspisR1PublicPreparation.sampler.qm31_sample block
      ok (.Ok q,after))
     apply NJM_ChildDomain.bind_good
     intro q
     trivial

/-- The actual Code carries exactly that domain, without erasing its log in
the parent association. Only the return projection is used by this lemma. -/
theorem code {H : Type} (D : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H)
 (record : r1_wire.ValidatedRecord) (bound : record.row.val≤24) :
 NJM_ChildDomain.Good (PreparedHashCode.run (S1SemanticCode.semanticValidated D t record)).2 := by
 rw [PreparedHashCode.run_value,S1SemanticCode.semanticValidated_erasure]
 exact source D t record bound

#print axioms source
#print axioms code
end AspisR1.NJM_SemanticDomain
