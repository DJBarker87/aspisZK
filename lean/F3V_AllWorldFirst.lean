import F3U_AllWorldMachine
import F3V_FirstCode
import F3U_ReifyFirst
import F3U_AsSliceBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_AllWorldFirst
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
      AspisR1CurrentCaller.verifier.candidate.tx1
        (GExp_FirstCode.installed (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std)
        (F3V_OracleDictionary.current H (currentDigest c))
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize () none=ok (.Ok saved) ∧
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref)=ok (.Ok ()) := by
  obtain ⟨pub,proof,semantic,saved,hpub,hproof,decoded,first,second⟩ :=
    F3U_AllWorldMachine.accepted c hashv s H accepted
  rw [F3V_FirstCode.same H _ _ _ hashv (currentDigest c)] at first
  rw [GExp_FirstSource.source
    (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std
    (F3U_Oracle.hashv H) (F3V_OracleDictionary.current H (currentDigest c)) (fun _=>rfl)
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize] at first
  exact ⟨pub,proof,semantic,saved,hpub,hproof,decoded,first,second⟩

#print axioms accepted
end AspisR1.F3V_AllWorldFirst
end
