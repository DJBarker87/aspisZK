import F3T_InitFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_InitHead
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem head (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (root : State) (word : LiteralTranscript.C1Word)
    (first : i.proof 0=.initial root word) (H : Bytes → State) :
    (eval H (F3_Model.verifier D i)).1.head?=
      some (PublicInitFrame.frame i.semantic.value.pubBytes root,H (PublicInitFrame.frame i.semantic.value.pubBytes root)) := by
  change (eval H (OracleDecisionFeasibilityCore.verifierFrom D _ i.proof 33
    (emptyPrefix i.semantic.value))).1.head?=_
  rw [OracleDecisionFeasibilityCore.verifierFrom]
  apply RawK_ModelHead.bind_head
  change (eval H (LiteralByteSampler.samp 0 _ (i.proof 0)).toProgram).1.head?=_
  rw [first,LiteralByteSampler.eval_eq]
  simp only [LiteralTranscript.samp,LiteralTranscript.erase,UnifiedSampler.samp,
    DuplexSamplers.initial,Sampler.toProgram,eval,mapView,List.map_cons,List.head?_cons,
    PublicInitFrame.addr,Addr.toBytes_ofBytes]
  all_goals rfl

#print axioms head
end AspisR1.F3T_InitHead
end
