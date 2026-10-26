import DrvC_CutAcceptance
import F3T_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_SourceAcceptance
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open DrvC_Installation S2W_NativeConsolidation F3T_ByteCarrier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Native same-cut acceptance reaches precisely the F3X source carrier.
The byte equalities are the existing authenticated-input obligations, not a
new clean-account transport premise. This is a pointwise bridge at H. -/
theorem installed {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (decoded : Port1_Driver.decodeSemantic (sdk c) f.pub = ok (some f.semantic))
    (proof : bytesOf s.proof.val = bytesOf f.proof.val)
    (pub : bytesOf s.pub.val = bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val = bytesOf saved.val) :
    (eval H (F3T_Installed.source c hashv
      (input c ⟨bytesOf f.pub.val,bytesOf f.proof.val⟩))).2 = true := by
  simp only [F3T_Installed.source,input,DrvC_Bytes.asSlice,decoded]
  exact DrvC_CutAcceptance.source_accepts c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts proof pub checkpoint

#print axioms installed
end AspisR1.SCG_SourceAcceptance
end
