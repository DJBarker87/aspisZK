import F3U_AsSliceBytes
import F3V_PairLog
import F3U_SourceInputs
import F3U_ReifyFirst
import F3V_FirstCode
import F3V_SecondComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_ByteLog
open Aeneas Aeneas.Std Result
open DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (s : F3T_ByteCarrier.Submission) (H : Bytes → State)
    (accepted : (eval H (F3T_Installed.source c hashv (F3T_ByteCarrier.input c s))).2=true) :
    ∃ (pub proof : Slice U8) (semantic : Port1_Driver.Semantic),
      MultiproofConeCanonical.bytesOf pub.val=s.publicBytes ∧ MultiproofConeCanonical.bytesOf proof.val=s.stored ∧
      Port1_Driver.decodeSemantic (sdk c) pub=ok (some semantic) ∧
    ∃ saved : alloc.vec.Vec U8,
      eval H (F3T_Installed.source c hashv (F3T_ByteCarrier.input c s))=
        (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
            c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
            pub proof 10#usize) []).2 ++
         SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref) []).2,true) := by
  obtain ⟨pub,proof,semantic,hpub,hproof,decoded,source,yes⟩ := F3U_SourceInputs.accepted c hashv s H accepted
  obtain ⟨saved,logs⟩ := F3V_PairLog.evaluated c hashv semantic pub proof H yes
  rw [←source] at logs
  exact ⟨pub,proof,semantic,F3U_AsSliceBytes.inverse _ _ hpub,F3U_AsSliceBytes.inverse _ _ hproof,decoded,saved,logs⟩

#print axioms accepted
end AspisR1.F3V_ByteLog
end
