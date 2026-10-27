import RPz8_ARU_WriterReached
import RPz8_SCH_FirstChild
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_FirstHeader
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize)
    (saved : alloc.vec.Vec U8)
    (success : AdapterRw.first_decoded (SCH_IdealSdk.dictionary c hashv H)
      semantic pub proof split = ok (.Ok saved)) :
    CPhy_Header.decode (MultiproofConeCanonical.bytesOf saved.val) =
      some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) ∧
    saved.val.length = 1768 := by
  let base := GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry
  let D := AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
    (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std))
  have first := SCH_FirstChild.accepted c hashv H semantic pub proof split saved success
  have source : CheckpointBytes5Effect.erase (SdkC_Source.dictionary (SCH_Oracle.ideal H)) ()
      (GExq_FirstCode.code base c.boundaries c.std (SCH_Oracle.ideal H) D
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split ()) = ok (.Ok saved) := by
    rw [←SdkC_Source.erasure (SCH_Oracle.ideal H) _ []]
    exact (SCH_Oracle.evaluation H _ []).1.trans first
  obtain ⟨p,a,writer,_⟩ := ARU_WriterReached.reached base c.boundaries c.std (SCH_Oracle.ideal H) D
    (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split () saved source
  apply ARU_WriterHeader.ideal H p a proof pub saved
  exact (SCH_Oracle.evaluation H _ []).1.symm.trans
    ((SdkC_Source.erasure (SCH_Oracle.ideal H) _ []).trans writer)

#print axioms accepted
end AspisR1.ARU_FirstHeader
end
