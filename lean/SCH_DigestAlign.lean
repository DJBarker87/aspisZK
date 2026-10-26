import SCH_InstalledStage
import SCH_SdkPure
set_option autoImplicit false
namespace AspisR1.SCH_DigestAlign

theorem source {F C : Type} (c : DrvC_Installation.Configuration F C)
    (err : C) (reservation : NP6_StdModel.Reservation) :
    let r := Rc5_Install.configuration err c reservation
    DrvC_Installation.digest r = AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
      (GExq_Caller.sdk r.adapter r.currentBase r.stageBase r.finish r.reserved r.query r.geometry r.boundaries r.std) := by
  dsimp only
  have aligned : AuS1_Install.base (Rc5_Install.configuration err c reservation).stageBase =
      (Rc5_Install.configuration err c reservation).stageBase := SCH_StageAlign.library _
  have same : DrvC_Installation.sdk (Rc5_Install.configuration err c reservation) =
      GExq_Caller.sdk (Rc5_Install.configuration err c reservation).adapter
        (Rc5_Install.configuration err c reservation).currentBase
        (Rc5_Install.configuration err c reservation).stageBase
        (Rc5_Install.configuration err c reservation).finish
        (Rc5_Install.configuration err c reservation).reserved
        (Rc5_Install.configuration err c reservation).query
        (Rc5_Install.configuration err c reservation).geometry
        (Rc5_Install.configuration err c reservation).boundaries
        (Rc5_Install.configuration err c reservation).std := by
    rw [DrvC_Installation.gexp_dictionary,aligned]
  exact congrArg AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 same

#print axioms source
end AspisR1.SCH_DigestAlign
