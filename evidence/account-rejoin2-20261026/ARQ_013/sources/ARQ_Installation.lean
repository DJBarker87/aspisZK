import FIp_Install
import SCH_DigestAlign
set_option autoImplicit false
namespace AspisR1.ARQ_Installation
open DrvC_Installation

/-- Exact Rc9 installed native dictionary and account child dictionary. -/
theorem dictionary {C : Type} (err : C) (base : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    let c := FIp_Install.configuration err base r
    sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std := by
  dsimp only
  rw [gexp_dictionary,SCH_StageAlign.library]

/-- Exact F3V accepted-branch base at the installed Rc9 instance. -/
theorem canonical_base {C : Type} (err : C) (base : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    FIp_Install.configuration err base r =
      F3V_Install.configuration
        (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r base)) r) := rfl

#print axioms dictionary
#print axioms canonical_base
end AspisR1.ARQ_Installation
