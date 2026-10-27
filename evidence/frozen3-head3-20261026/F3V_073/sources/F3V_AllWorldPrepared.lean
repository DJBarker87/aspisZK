import F3V_FirstRun
import F3V_Install
import F3V_PreparedFacts
import F3V_IdealBackend
import F3V_Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_AllWorldPrepared
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

theorem accepted {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (decoder : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (accepted : (eval H (F3T_Installed.source (F3V_Install.configuration base) hashv (input (F3V_Install.configuration base) s))).2=true) :
    let c := F3V_Install.configuration base
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
          (F3V_StageDictionary.ideal H (digest c)) pub proof saved.deref () none=ok (.Ok ()) ∧
        F3V_PreparedFacts.Facts (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry
          base.boundaries c.std (F3V_OracleDictionary.current H (currentDigest c)) semantic pub proof run.p run.zero H := by
  dsimp only
  let c := F3V_Install.configuration base
  obtain ⟨pub,proof,semantic,saved,hpub,hproof,decoded,header,canonical,run,zero,second⟩ :=
    F3V_FirstRun.accepted c hashv s H accepted
  obtain ⟨statement,decode,valid,selected⟩ := F3V_Decoded.fields (sdk c) pub semantic decoded
  have facts := F3V_PreparedAdmitted.from_run c (Op5T_Concrete.current c.currentBase) c.reserved
    c.query c.geometry base.boundaries c.std _ statement semantic pub proof 10#usize saved decode selected
    run header H (F3V_IdealBackend.backend H (currentDigest c)) w canonical decoder
  exact ⟨pub,proof,semantic,saved,hpub,hproof,decoded,header,canonical,run,zero,second,facts⟩

#print axioms accepted
end AspisR1.F3V_AllWorldPrepared
end
