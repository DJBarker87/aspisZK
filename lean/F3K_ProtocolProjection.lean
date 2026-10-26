import F3K_SamplerProtocol
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_ProtocolProjection
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw

theorem source (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat)
    (log : List (Bytes × State)) (state : State)
    (hlog : (eval H (F3J_SamplerRun.program pf 0 n (FS.emptyPrefix pub))).1=log)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program pf 0 n (FS.emptyPrefix pub))).2)=state) :
    ((List.range n).map (fun j=>(eval H
      ((LiteralByteProtocol.protocol D).chain H pub pf j).toProgram).1)).flatten=log ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf n))=state := by
  have protocol := F3K_SamplerProtocol.initial D H pub pf n
  exact ⟨(congrArg Prod.fst protocol).symm.trans hlog,
    (congrArg (fun r=>UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix r.2)) protocol).symm.trans hstate⟩

#print axioms source
end AspisR1.F3K_ProtocolProjection
end
