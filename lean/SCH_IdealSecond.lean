import SCH_SecondChild
import SCH_InstalledStage
import SCH_DigestAlign
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_IdealSecond
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (pub proof checkpoint : Slice U8) :
    let r := Rc5_Install.configuration err c reservation
    (SCH_IdealSdk.dictionary r hashv H).op11
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary r hashv H))
      pub proof checkpoint () none = ok (.Ok ()) →
    (eval H (GExp_Experiment.second (DrvC_Installation.stage r) r.reserved hashv
      (DrvC_Installation.digest r) ⟨pub,proof,checkpoint⟩)).2 = ok (.Ok ()) := by
  dsimp only
  intro success
  have result := SCH_SecondChild.accepted (Rc5_Install.configuration err c reservation) hashv H
    pub proof checkpoint success
  rw [SCG_SecondCode.code,← SCH_DigestAlign.source c err reservation,SCH_InstalledStage.same] at result
  exact result

#print axioms accepted
end AspisR1.SCH_IdealSecond
end
