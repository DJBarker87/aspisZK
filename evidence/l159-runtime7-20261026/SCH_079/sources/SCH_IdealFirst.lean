import SCH_FirstChild
import SCH_IdealSplit
import SCH_DigestAlign
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_IdealFirst
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize)
    (saved : alloc.vec.Vec U8) :
    let r := Rc5_Install.configuration err c reservation
    AdapterRw.first_decoded (SCH_IdealSdk.dictionary r hashv H)
      semantic pub proof split = ok (.Ok saved) →
    (eval H (GExp_Experiment.first
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry) r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r)
      ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩)).2 = ok (.Ok saved) := by
  dsimp only
  intro success
  have first := SCH_FirstChild.accepted (Rc5_Install.configuration err c reservation) hashv H semantic pub proof split saved success
  have selected := SCH_IdealSplit.split _ _ _ hashv _ _ pub proof split saved H first
  rw [selected,SCG_FirstCode.code,← SCH_DigestAlign.source c err reservation] at first
  exact first

#print axioms accepted
end AspisR1.SCH_IdealFirst
end
