import RPz7_F3V_Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_FirstRun
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    ∃ (pub proof : Slice U8) (semantic : Port1_Driver.Semantic) (saved : alloc.vec.Vec U8),
      bytesOf pub.val=s.publicBytes ∧ bytesOf proof.val=s.stored ∧
      Port1_Driver.decodeSemantic (sdk c) pub=ok (some semantic) ∧
      OraclePortHeader.accepts (bytesOf proof.val)=true ∧
      OraclePortCompactDraft.scan (bytesOf proof.val) ∧
      ∃ run : Tx1Q_Execution.Run
        (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std)
        c.reserved c.query c.geometry (F3V_OracleDictionary.current H (currentDigest c)) ()
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize saved,
        AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO
          (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std)=ok run.zero ∧
        VTop_Stages.verifier.candidate.tx2_authenticated
          (GExp_SecondCode.installed (stage c) c.reserved)
          (F3V_StageDictionary.ideal H (digest c)) pub proof saved.deref () none=ok (.Ok ()) := by
  obtain ⟨pub,proof,semantic,saved,hpub,hproof,decoded,first,second⟩ := F3V_AllWorldPair.accepted c hashv s H accepted
  have parser := F3V_Parser.accepted c.currentBase c.reserved c.query c.geometry c.boundaries c.std
    _ () (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof saved first
  rw [F3V_FirstSlots.same] at first
  have constants := SdkD_FoldedCut.installed_constants (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
  rw [Uni_Install.compose_tx1] at constants
  obtain ⟨run,zero,view,range,copy⟩ := SdkD_Tx1Run.accepted _ c.reserved c.query c.geometry _ ()
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize saved
    (Tx1Q_Execution.actual_slots _ _ _ _ _ _) constants.1 constants.2 first
  exact ⟨pub,proof,semantic,saved,hpub,hproof,decoded,parser.1,parser.2,run,zero,second⟩

#print axioms accepted
end AspisR1.F3V_FirstRun
end
