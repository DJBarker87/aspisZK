import RPz7_F3U_ReifyFirst
import RPz7_F3U_AsSliceBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AllWorldMachine
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
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
          pub proof 10#usize)=ok (.Ok saved) ∧
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref)=ok (.Ok ()) := by
  obtain ⟨pub,proof,semantic,hpub,hproof,decoded,source,ha⟩ := F3U_SourceInputs.accepted c hashv s H accepted
  obtain ⟨saved,first,second⟩ := F3U_ReifyFirst.first c hashv semantic pub proof H ha
  exact ⟨pub,proof,semantic,saved,F3U_AsSliceBytes.inverse _ _ hpub,
    F3U_AsSliceBytes.inverse _ _ hproof,decoded,first,second⟩

#print axioms accepted
end AspisR1.F3U_AllWorldMachine
end
