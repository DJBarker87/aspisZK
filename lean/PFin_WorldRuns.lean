import F3V_RunEvidence
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldRuns
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem accepted {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (decoder : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (accepted : (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv
      (input (F3V_Install.configuration base) s))).2=true) :
    ∃ e : Evidence (F3V_Install.configuration base) base.boundaries s H,
      AspisR1CurrentCaller.verifier.candidate.tx1
        (GExp_FirstCode.installed (GExp_FirstPair.base (F3V_Install.configuration base).currentBase
          (F3V_Install.configuration base).reserved (F3V_Install.configuration base).query (F3V_Install.configuration base).geometry)
          (F3V_Install.configuration base).boundaries (F3V_Install.configuration base).std)
        (D1 (F3V_Install.configuration base) H) (AspisS6CurrentVerifierCarrier.toPublic e.semantic)
        e.pub e.proof 10#usize () none=ok (.Ok e.saved) := by
  let c := F3V_Install.configuration base
  obtain ⟨pub,proof,semantic,saved,hpub,hproof,decoded,first,second⟩ :=
    F3V_AllWorldPair.accepted c hashv s H accepted
  have parser := F3V_Parser.accepted c.currentBase c.reserved c.query c.geometry c.boundaries c.std
    _ () (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof saved first
  have firstSource := first
  rw [F3V_FirstSlots.same] at first
  have constants := SdkD_FoldedCut.installed_constants (Uni_Install.current c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
  rw [Uni_Install.compose_tx1] at constants
  obtain ⟨run,zero,view,range,copy⟩ := SdkD_Tx1Run.accepted _ c.reserved c.query c.geometry _ ()
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize saved
    (Tx1Q_Execution.actual_slots _ _ _ _ _ _) constants.1 constants.2 first
  obtain ⟨statement,decode,valid,selected⟩ := F3V_Decoded.fields (sdk c) pub semantic decoded
  have facts := F3V_PreparedAdmitted.from_run c (Op5T_Concrete.current c.currentBase) c.reserved
    c.query c.geometry base.boundaries c.std _ statement semantic pub proof 10#usize saved decode selected
    run parser.1 H (F3V_IdealBackend.backend H (currentDigest c)) w parser.2 decoder
  exact ⟨⟨pub,proof,semantic,saved,hpub,hproof,decoded,parser.1,parser.2,run,zero,view,range,copy,second,facts⟩,firstSource⟩

#print axioms accepted
end AspisR1.PFin_WorldRuns
end
