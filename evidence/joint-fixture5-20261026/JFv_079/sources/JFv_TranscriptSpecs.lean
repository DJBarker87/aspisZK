import JFv_OracleTotal
set_option autoImplicit false
namespace AspisR1.JFv_TranscriptSpecs
open Aeneas Aeneas.Std Result WP
open AspisR1PublicPreparation

@[step] theorem record (pre : r1_wire.Prefix) (row : U8) (bound : row.val<27) :
    r1_wire.Prefix.validated_record pre row
      ⦃ out => ∃ vr,out=.Ok vr ∧ vr.row=row ⦄ := by
  obtain ⟨frame,read⟩ := JFv_PrefixRecord.record pre row bound
  have call : r1_wire.Prefix.validated_record pre row=ok (.Ok ⟨row,frame⟩) := by
    simp only [r1_wire.Prefix.validated_record,read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  rw [call,WP.spec_ok]
  exact ⟨⟨row,frame⟩,rfl,rfl⟩

@[step] theorem semantic {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (t : r1_wire.SemanticTranscript H) (vr : r1_wire.ValidatedRecord)
    (same : vr.row=t.next_row) (bound : vr.row.val<25) :
    r1_wire.SemanticTranscript.semantic_validated D t vr
      ⦃ out => ∃ q after,out=(.Ok q,after) ∧ after.next_row.val=vr.row.val+1 ∧
        JFv_RoundArithmetic.Canonical q ⦄ := by
  obtain ⟨q,after,call,next,canon⟩ := JFv_SemanticCall.success D total t vr same bound
  rw [call,WP.spec_ok]
  exact ⟨q,after,rfl,next,canon⟩

#print axioms record
#print axioms semantic
end AspisR1.JFv_TranscriptSpecs
