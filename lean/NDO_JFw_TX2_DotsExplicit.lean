import NDO_JFv_TX2_DotsMeaning
import NDO_JFv_TX2_EbyKFinishMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_DotsExplicit
open Aeneas Aeneas.Std Result
/-- Source-defined value identification, before numeric coordinate instantiation. -/
theorem chosen (i : Fin 12) (out : Array FIo_Install.NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots
      (JFo_Opening.value (JFn_Values.position i)) JFr_TX2_FirstLane.native=ok out) :
    JFs_TX2_Dots.value i=FIp_DotsAdapter.fromArray out := by
  have same := Result.ok.inj ((JFs_TX2_Dots.native i).symm.trans run)
  exact congrArg FIp_DotsAdapter.fromArray same
#print axioms chosen
end AspisR1.JFw_TX2_DotsExplicit
end
