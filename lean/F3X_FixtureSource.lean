import DrvC_CutAcceptance
import F3T_Installed
import F3U_Slice
import S2W_AuthenticatedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_FixtureSource
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier S2W_NativeConsolidation

/-- The byte source is genuinely accepted on the same symbolic native fixture.
No source acceptance, model acceptance or whole-log equality is a premise. -/
theorem accepted {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 : Slice U8) (saved : alloc.vec.Vec U8)
    (nativeAccepted : native1 id accounts1 data1=ok (.Ok saved))
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (sameProof : bytesOf s.proof.val=bytesOf f.proof.val)
    (samePublic : bytesOf s.pub.val=bytesOf f.pub.val)
    (sameCheckpoint : bytesOf s.checkpoint.val=bytesOf saved.val) :
    (eval H (F3T_Installed.source c hashv
      (input c ⟨bytesOf f.pub.val,bytesOf f.proof.val⟩))).2=true := by
  have sourceAccepted := (extraction.stage1 id accounts1 data1).symm.trans nativeAccepted
  obtain ⟨semantic,decoded,newcuts⟩ := DrvC_DecodeCut.same_cut c id accounts1 accounts2 data1 saved f s sourceAccepted cuts
  have pair := DrvC_CutAcceptance.source_accepts c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved {f with semantic:=semantic} s newcuts sameProof samePublic sameCheckpoint
  simp only [F3T_Installed.source,input,F3U_Slice.roundtrip,decoded]
  exact pair

#print axioms accepted
end AspisR1.F3X_FixtureSource
end
