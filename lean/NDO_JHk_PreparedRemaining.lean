import NDO_JHe_ImmutableState
import NDO_JHe_CurrentWriterImage
import NDO_JGp_CurrentRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHk_PreparedRemaining
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry JHe_CurrentWriterImage
def queryBytes : List U8 := JFq_QueryWords.b0.val ++ JFq_QueryWords.b1.val ++ JFq_QueryWords.b2.val ++ JFq_QueryWords.b3.val ++ JFq_QueryWords.b4.val ++ JFq_QueryWords.b5.val ++ JFq_QueryWords.b6.val ++ JFq_QueryWords.b7.val ++ JFq_QueryWords.b8.val ++ JFq_QueryWords.b9.val ++ JFq_QueryWords.b10.val ++ JFq_QueryWords.b11.val ++ JFq_QueryWords.b12.val ++ JFq_QueryWords.b13.val ++ JFq_QueryWords.b14.val ++ JFq_QueryWords.b15.val ++ JFq_QueryWords.b16.val ++ JFq_QueryWords.b17.val ++ JFq_QueryWords.b18.val ++ JFq_QueryWords.b19.val ++ JFq_QueryWords.b20.val ++ JFq_QueryWords.b21.val

theorem word (q : U32) :
    (MultiproofConeCanonical.bytesOf (core.num.U32.to_le_bytes q).val).map CheckpointBytes5Writer.u8=
      (OraclePortCompactDraft.le32 q.val).map CheckpointBytes5Writer.u8 :=
  congrArg (List.map CheckpointBytes5Writer.u8) (CheckpointP6KBytes.word_bytes q)
#print axioms word

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    (MultiproofConeCanonical.bytesOf (prepared p).state.val).map CheckpointBytes5Writer.u8=JFq_State.bytes ∧
    ((prepared p).roots.val.flatMap (fun r => MultiproofConeCanonical.bytesOf r.val)).map
      CheckpointBytes5Writer.u8=JFq_Root0.bytes++JFq_Root1.bytes ∧
    ((prepared p).queries.val.flatMap (fun q => MultiproofConeCanonical.bytesOf
      (core.num.U32.to_le_bytes q).val)).map CheckpointBytes5Writer.u8=queryBytes := by
  have state := JHe_ImmutableState.source p input scratch prepare
  have roots := JGp_CurrentRoots.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  have queries := JGp_CurrentQueries.source _ _ _ JGn_TerminalIdentified.shaDictionary () p input scratch prepare
  constructor
  · change (MultiproofConeCanonical.bytesOf p.state.val).map _=_
    rw [state,WAdm_SourceWriter.map_bytes]
    rfl
  constructor
  · change (p.roots.val.flatMap (fun r => MultiproofConeCanonical.bytesOf r.val)).map _=_
    rw [roots]
    simp only [JFo_Prepared.value,Array.make,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.map_append,WAdm_SourceWriter.map_bytes]
    rfl
  · change (p.queries.val.flatMap (fun q => MultiproofConeCanonical.bytesOf
      (core.num.U32.to_le_bytes q).val)).map _=_
    rw [queries]
    simp only [JFq_Queries.value,Array.make,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.map_append,word]
    rfl
#print axioms source
end AspisR1.JHk_PreparedRemaining
end
