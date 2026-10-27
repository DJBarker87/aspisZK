import RPz8_SCH_StageAlign
set_option autoImplicit false
namespace AspisR1.SCH_InstalledStage

theorem same {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation) :
    let r := Rc5_Install.configuration err c reservation
    GExp_SecondPair.base r.stageBase r.finish r.reserved r.query r.geometry =
      DrvC_Installation.stage r := by
  dsimp only
  have aligned : AuS1_Install.base (Rc5_Install.configuration err c reservation).stageBase =
      (Rc5_Install.configuration err c reservation).stageBase := SCH_StageAlign.library _
  rw [DrvC_Installation.stage_dictionary,aligned]

#print axioms same
end AspisR1.SCH_InstalledStage
