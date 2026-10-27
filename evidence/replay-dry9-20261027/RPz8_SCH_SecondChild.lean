import RPz8_SCH_SdkPure
import RPz8_SCG_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_SecondChild
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] GExq_SecondCode.code

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (pub proof checkpoint : Slice U8)
    (success : (SCH_IdealSdk.dictionary c hashv H).op11
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary c hashv H))
      pub proof checkpoint () none = ok (.Ok ())) :
    (eval H (SdkC_Oracle.program (GExq_SecondCode.code
      (GExp_SecondPair.base c.stageBase c.finish c.reserved c.query c.geometry) c.reserved hashv
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std))
      pub proof checkpoint ()))).2 = ok (.Ok ()) := by
  rw [SCH_SdkPure.digest] at success
  dsimp only [SCH_IdealSdk.dictionary,GExq_ChildCode.execute] at success
  exact success

#print axioms accepted
end AspisR1.SCH_SecondChild
end
