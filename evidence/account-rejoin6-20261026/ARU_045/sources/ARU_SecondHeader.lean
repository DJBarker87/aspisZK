import ARU_ReaderReached
import SCH_SecondChild
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_SecondHeader
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (pub proof ck : Slice U8)
    (success : (SCH_IdealSdk.dictionary c hashv H).op11
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary c hashv H))
      pub proof ck () none = ok (.Ok ())) :
    CPhy_Header.decode (MultiproofConeCanonical.bytesOf ck.val) =
      some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
  let base := GExp_SecondPair.base c.stageBase c.finish c.reserved c.query c.geometry
  let D := AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
    (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std)
  have second := SCH_SecondChild.accepted c hashv H pub proof ck success
  have source : CheckpointBytes5Effect.erase (SdkC_Source.dictionary (SCH_Oracle.ideal H)) ()
      (GExq_SecondCode.code base c.reserved (SCH_Oracle.ideal H) D pub proof ck ()) = ok (.Ok ()) := by
    rw [←SdkC_Source.erasure (SCH_Oracle.ideal H) _ []]
    exact (SCH_Oracle.evaluation H _ []).1.trans second
  obtain ⟨p,a,reader⟩ := ARU_ReaderReached.reached base c.reserved (SCH_Oracle.ideal H) D () pub proof ck source
  apply ARU_ReaderHeader.ideal c.reserved H ck proof pub p a
  exact (SCH_Oracle.evaluation H _ []).1.symm.trans
    ((SdkC_Source.erasure (SCH_Oracle.ideal H) _ []).trans reader)

#print axioms accepted
end AspisR1.ARU_SecondHeader
end
