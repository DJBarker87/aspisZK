import RPz7_DrvC_Bytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_AcceptedCalls
open Aeneas Aeneas.Std Result
open DrvC_Installation S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem current_success {F C : Type} (c : Configuration F C) (semantic : Port1_Driver.Semantic)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded (sdk c) semantic pub proof split = ok (.Ok saved)) :
    AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
      (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split () none = ok (.Ok saved) :=
  AspisS6CurrentFirstInstallation.current_success _ _ semantic pub proof split () saved
    (AspisS6CurrentStage1CodecJoin.first_success _ semantic pub proof split saved accepted)

theorem split {F C : Type} (c : Configuration F C) (semantic : Port1_Driver.Semantic)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded (sdk c) semantic pub proof split = ok (.Ok saved)) :
    split = 10#usize := by
  have facts := AspisR1CurrentCaller.Tx1Reachability.tx1_success _ _
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split () saved
    (current_success c semantic pub proof split saved accepted)
  simpa only [AspisR1CurrentCaller.compact.SPLIT] using facts.1

theorem first {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded (sdk c) semantic pub proof 10#usize = ok (.Ok saved)) :
    (eval H (GExp_Experiment.first
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv (currentDigest c)
      ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩)).2 = ok (.Ok saved) := by
  have success := current_success c semantic pub proof 10#usize saved accepted
  rw [current_dictionary] at success
  have result := GExp_FirstAccepted.accepted _ c.boundaries c.std hashv (currentDigest c)
    (S2W_DigestExtraction.native_binding _ native1 native2 hashv extraction ())
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize saved sha256 H p1 syscall success
  exact congrArg Prod.snd result

theorem second {F C : Type} (c : Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdk c) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts (sdk c) accounts1 accounts2 saved f s) :
    (eval H (GExp_Experiment.second (stage c) c.reserved hashv (digest c) ⟨s.pub,s.proof,s.checkpoint⟩)).2 =
      ok (.Ok ()) := by
  have returned := GExp_SecondPair.same_pair c.adapter c.currentBase (AuS1_Install.base c.stageBase)
    c.finish c.reserved c.query c.geometry c.boundaries c.std native1 native2 hashv extraction
    sha256 H p1 syscall accounts1 accounts2 saved f s cuts
  exact congrArg Prod.snd returned.2.1

#print axioms current_success
#print axioms split
#print axioms first
#print axioms second
end AspisR1.DrvC_AcceptedCalls
end
