import RPz7_DrvC_DecodeCut
import RPz7_DrvC_SourceEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_CutAcceptance
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem source_accepts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (proof : bytesOf s.proof.val = bytesOf f.proof.val)
    (pub : bytesOf s.pub.val = bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val = bytesOf saved.val) :
    (eval H (DrvC_PairProgram.source c hashv f.semantic f.pub f.proof)).2 = true := by
  have sp := DrvC_AcceptedCalls.split c f.semantic f.pub f.proof f.split saved cuts.first
  have first := cuts.first
  rw [sp] at first
  have one := DrvC_AcceptedCalls.first c native1 native2 hashv extraction sha256 H p1 syscall
    f.semantic f.pub f.proof saved first
  have two := DrvC_AcceptedCalls.second c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts
  have hp := DrvC_Bytes.slice_injective s.proof f.proof proof
  have hu := DrvC_Bytes.slice_injective s.pub f.pub pub
  have hc := DrvC_Bytes.slice_injective s.checkpoint saved.deref checkpoint
  rw [hp,hu,hc] at two
  simp only [DrvC_PairProgram.source,eval_bind,one,two,Port1_Driver.verdict,eval]

theorem driver_accepts {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (sdk (DrvC_FirstConstants.configuration c)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (sdk (DrvC_FirstConstants.configuration c)) accounts1 accounts2 saved f s)
    (decoded : Port1_Driver.decodeSemantic (sdk (DrvC_FirstConstants.configuration c)) f.pub = ok (some f.semantic))
    (proof : bytesOf s.proof.val = bytesOf f.proof.val)
    (pub : bytesOf s.pub.val = bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val = bytesOf saved.val)
    (i : OraclePortStoredExperimentC4.Input)
    (publicCarrier : i.statement.pubBytes = bytesOf f.pub.val) (proofCarrier : i.stored = bytesOf f.proof.val) :
    (eval H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) i)).2 = true := by
  rw [DrvC_SourceEntry.same_program c hashv]
  simp only [DrvC_SourceEntry.source,publicCarrier,proofCarrier,DrvC_Bytes.asSlice,decoded]
  exact source_accepts _ native1 native2 hashv extraction sha256 H p1 syscall accounts1 accounts2 saved f s cuts proof pub checkpoint

#print axioms source_accepts
#print axioms driver_accepts
end AspisR1.DrvC_CutAcceptance
end
