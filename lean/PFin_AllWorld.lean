import F3V_AllWorldInput
import PFin_Packet
import PFin_Gates
import F3V_FirstRun
import F3V_SourceInput
import F3V_IdealBackend
import F3V_Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_AllWorld
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : Submission) (H : Bytes → State)
    (w : CanonicalCutEnrichedTranscript.Words)
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
          (F3V_StageDictionary.ideal H (digest c)) pub proof saved.deref () none=ok (.Ok ()) ∧
        PFin_Packet.Facts (bytesOf pub.val) (bytesOf proof.val) (Tx1Q_Carriers.prepared run.p) H := by
  obtain ⟨pub,proof,semantic,saved,hpub,hproof,decoded,header,canonical,run,zero,second,i,facts⟩ :=
    F3V_AllWorldInput.accepted c hashv s H w accepted
  obtain ⟨physical,stored,p,q,source,out,v,sourceView,sem,scratch,parser,queries,found,prepare,rest⟩ := facts
  have reached := parser
  rw [stored] at reached
  have gates := PFin_Gates.closed _ p q _ source reached found queries
  exact ⟨pub,proof,semantic,saved,hpub,hproof,decoded,header,canonical,run,zero,second,
    i,p,q,source,physical,stored,reached,gates.1,queries,found,gates.2.1,gates.2.2,prepare⟩

#print axioms accepted
end AspisR1.PFin_AllWorld
end
