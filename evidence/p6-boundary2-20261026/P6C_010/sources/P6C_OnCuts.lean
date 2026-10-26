import P6C_Batches
import DrvC_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_OnCuts
open Aeneas Aeneas.Std Result SdkC_Source
open S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def SafeBatches {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : Parts → Result Digest) (H : Bytes → State) (f : FirstCut) (s : SecondCut) : Prop :=
  ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Array U8 32#usize)
    (p2 : VTop_Stages.verifier.Prepared) (root2 : Array U8 32#usize),
    P6C_Pair.Safe hashv H (SdkC_BatchSource.currentCode hashv f.proof p0 root0) (.Ok ()) ∧
    P6C_Pair.Safe hashv H (SdkC_BatchSource.stageCode hashv s.proof p2 root2) (.Ok ()) ∧
    run (P6C_Batches.extended hashv H)
      (SdkC_BatchSource.currentCode (P6C_Batches.extended hashv H) f.proof p0 root0) [] =
      run hashv (SdkC_BatchSource.currentCode hashv f.proof p0 root0) [] ∧
    run (P6C_Batches.extended hashv H)
      (SdkC_BatchSource.stageCode (P6C_Batches.extended hashv H) s.proof p2 root2) [] =
      run hashv (SdkC_BatchSource.stageCode hashv s.proof p2 root2) []

/-- Universally quantified over cuts, so this applies to the existing top
result's very same existential witnesses, without selecting a second pair. -/
theorem same_cuts {F C : Type} (c : DrvC_Installation.Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : Parts → Result Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (DrvC_Installation.sdk c) accounts1 accounts2 saved f s) :
    SafeBatches c hashv H f s := by
  rw [DrvC_Installation.aus1_dictionary] at extraction cuts
  obtain ⟨p0,root0,p2,root2,first,second⟩ := SdkC_BatchPair.same_pair c.adapter
    (Uni_Install.base c.currentBase c.reserved c.query c.geometry)
    (SdkD_Install.stage c.stageBase c.reserved c.query c.geometry)
    c.finish c.boundaries c.std native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts
  exact ⟨p0,root0,p2,root2,P6C_Pair.safe hashv H _ _ first,
    P6C_Pair.safe hashv H _ _ second,
    P6C_Batches.current hashv H _ _ _ first.1,P6C_Batches.stage hashv H _ _ _ second.1⟩

#print axioms same_cuts
end AspisR1.P6C_OnCuts
end
