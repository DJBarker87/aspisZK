import DrvC_CutAcceptance
import F3U_FirstCode
import F3U_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_PairLog
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem evaluated {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (proof : bytesOf s.proof.val=bytesOf f.proof.val) (pub : bytesOf s.pub.val=bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val=bytesOf saved.val) :
    eval H (DrvC_PairProgram.source c hashv f.semantic f.pub f.proof)=
      (SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic f.semantic)
          f.pub f.proof f.split) []).2 ++
       SdkC_Source.readLog (SdkC_Source.run hashv
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) s.pub s.proof s.checkpoint) []).2,true) := by
  have first := DrvC_AcceptedCalls.current_success c f.semantic f.pub f.proof f.split saved cuts.first
  rw [current_dictionary] at first
  have one := GExp_FirstAccepted.accepted _ c.boundaries c.std hashv (currentDigest c)
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved sha256 H p1 syscall first
  have two := (GExp_SecondPair.same_pair c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std native1 native2 hashv extraction
    sha256 H p1 syscall accounts1 accounts2 saved f s cuts).2.1
  have hp := DrvC_Bytes.slice_injective s.proof f.proof proof
  have hu := DrvC_Bytes.slice_injective s.pub f.pub pub
  have hc := DrvC_Bytes.slice_injective s.checkpoint saved.deref checkpoint
  have split := DrvC_AcceptedCalls.split c f.semantic f.pub f.proof f.split saved cuts.first
  rw [split] at one ⊢
  change eval H (GExp_Experiment.first
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv (currentDigest c)
    ⟨AspisS6CurrentVerifierCarrier.toPublic f.semantic,f.pub,f.proof,10#usize⟩)=_ at one
  change eval H (GExp_Experiment.second (stage c) c.reserved hashv (digest c)
    ⟨s.pub,s.proof,s.checkpoint⟩)=_ at two
  rw [hp,hu,hc] at two ⊢
  simp only [DrvC_PairProgram.source,eval_bind,one,two,Port1_Driver.verdict,eval,List.append_nil]

#print axioms evaluated
end AspisR1.F3U_PairLog
end
