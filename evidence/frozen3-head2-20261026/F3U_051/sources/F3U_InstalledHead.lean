import F3U_PairLog
import F3U_FirstHead
import F3U_OracleHead
import F3U_SemanticBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_InstalledHead
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_ByteCarrier

theorem head {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s)
    (decoded : Port1_Driver.decodeSemantic (sdk c) f.pub=ok (some f.semantic))
    (proof : bytesOf s.proof.val=bytesOf f.proof.val) (pub : bytesOf s.pub.val=bytesOf f.pub.val)
    (checkpoint : bytesOf s.checkpoint.val=bytesOf saved.val) :
    ∃ (encoded : alloc.vec.Vec U8) (root : State),
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))=ok (.Ok encoded) ∧
      (eval H (F3T_Installed.source c hashv (input c ⟨bytesOf f.pub.val,bytesOf f.proof.val⟩))).1.head?=
        some (PublicInitFrame.frame (bytesOf encoded.val) root,H (PublicInitFrame.frame (bytesOf encoded.val) root)) := by
  have law := S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction
  have first := DrvC_AcceptedCalls.current_success c f.semantic f.pub f.proof f.split saved cuts.first
  rw [current_dictionary] at first
  have raw := (GExq_FirstSource.source _ c.boundaries c.std hashv (currentDigest c) () law
    (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split).trans first
  obtain ⟨encoded,root,state,serialized,firstHead⟩ := F3U_FirstHead.first _ c.boundaries c.std hashv
    (currentDigest c) law (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split () saved raw
  have pair := F3U_PairLog.evaluated c native1 native2 hashv extraction sha256 H p1 syscall
    accounts1 accounts2 saved f s cuts proof pub checkpoint
  have headPair : (eval H (DrvC_PairProgram.source c hashv f.semantic f.pub f.proof)).1.head?=
      some (PublicInitFrame.frame (bytesOf encoded.val) root,state) := by
    rw [congrArg Prod.fst pair]
    unfold RawK_CodeHead.head at firstHead
    rw [F3U_FirstCode.same] at firstHead
    exact RawK_ModelHead.append_head _ _ _ firstHead
  have answer := F3U_OracleHead.answer _ H _ state headPair
  rw [answer] at headPair
  refine ⟨encoded,root,serialized,?_⟩
  simpa only [F3T_Installed.source,input,F3U_Slice.roundtrip,decoded] using headPair

#print axioms head
end AspisR1.F3U_InstalledHead
end
