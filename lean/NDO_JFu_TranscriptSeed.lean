import NDO_JFv_TranscriptInitial
set_option autoImplicit false
namespace AspisR1.JFu_TranscriptSeed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (bytes : Slice U8) (root : Array U8 32#usize) (length : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len bytes)=ok (.Ok length)) (state : Array U8 32#usize)
    (digest : D.digest hash (TranscriptStep.initParts bytes root length)=ok state) :
    r1_wire.SemanticTranscript.new D hash bytes root=
      ok (.Ok (⟨state,hash,0#u8⟩ : r1_wire.SemanticTranscript H)) := by
  rw [TranscriptStep.new_of_length D hash bytes root length converted,digest,bind_tc_ok]

/-- Semantic serialization, rather than physical ASF8, is the initializer's byte input. -/
theorem public_source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (encoded : alloc.vec.Vec U8)
    (serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded))
    (root : Array U8 32#usize) (length : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len (alloc.vec.Vec.deref encoded))=ok (.Ok length))
    (state : Array U8 32#usize)
    (digest : D.digest hash (TranscriptStep.initParts (alloc.vec.Vec.deref encoded) root length)=ok state) :
    r1_semantic.public_transcript D pub hash root=
      ok (.Ok (⟨state,hash,0#u8⟩ : r1_wire.SemanticTranscript H)) := by
  unfold r1_semantic.public_transcript
  simp only [serialized,bind_tc_ok,core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]
  exact source D hash _ root length converted state digest

#print axioms source
#print axioms public_source
end AspisR1.JFu_TranscriptSeed
