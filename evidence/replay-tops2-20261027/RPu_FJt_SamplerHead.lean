import RPu_FJq_AlignedMessages
import RPz8_F3T_InitFrame
import RawK_ModelHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_SamplerHead
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem head (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (pub : LiteralTranscript.Public) (root : State)
    (initial : LiteralTranscript.erase (pf 0)=.initial root) :
    (eval H (F3J_SamplerRun.program pf 0 33 (emptyPrefix pub))).1.head?=
      some (PublicInitFrame.frame pub.pubBytes root,H (PublicInitFrame.frame pub.pubBytes root)) := by
  have first : (eval H (LiteralByteSampler.samp 0 (emptyPrefix pub) (pf 0)).toProgram).1.head?=
      some (PublicInitFrame.frame pub.pubBytes root,H (PublicInitFrame.frame pub.pubBytes root)) := by
    rw [LiteralByteSampler.eval_eq]
    simp only [LiteralTranscript.samp,initial,UnifiedSampler.samp,
      DuplexSamplers.initial,Sampler.toProgram,eval,mapView,List.map_cons,List.head?_cons,
      PublicInitFrame.addr,Addr.toBytes_ofBytes]
    rfl
  rw [F3J_SamplerStep.step H pf 0 32 (emptyPrefix pub)]
  exact RawK_ModelHead.append_head _ _ _ first

#print axioms head
end AspisR1.FJt_SamplerHead
end
