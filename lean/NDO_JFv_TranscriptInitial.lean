import NDO_JFv_OracleTotal
import RPz7_ExtractedDigest32Transcript
set_option autoImplicit false
namespace AspisR1.JFv_TranscriptInitial
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem success {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (hash : H) (bytes : Slice U8) (root : Array U8 32#usize) (length : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len bytes)=ok (.Ok length)) :
    ∃ t,r1_wire.SemanticTranscript.new D hash bytes root=ok (.Ok t) ∧ t.next_row.val=0 := by
  obtain ⟨state,call⟩ := total hash (TranscriptStep.initParts bytes root length)
  refine ⟨⟨state,hash,0#u8⟩,?_,rfl⟩
  rw [TranscriptStep.new_of_length D hash bytes root length converted,call,bind_tc_ok]

#print axioms success
end AspisR1.JFv_TranscriptInitial
