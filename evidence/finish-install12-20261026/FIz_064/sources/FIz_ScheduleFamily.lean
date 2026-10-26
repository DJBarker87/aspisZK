import FIz_ScheduleInitial
import FIz_ScheduleAbsorption
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScheduleFamily
open FIv_NativeValue (K)
open FIw_PublicModel (Public Openings Selectors)
theorem value (p : Public) (o : Openings) (s : Selectors)
    (hm : (∑ h : Fin 64, FIv_NativeArray.value s.high h.val)=1)
    (lm : (∑ l : Fin 16, FIv_NativeArray.value s.low l.val)=1) :
    List.ofFn (FIx_ScheduleModel.initial p.variant s o)++List.ofFn (FIx_ScheduleModel.absorption p.variant s o)=
      R0P.scheduleFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  rw [FIz_ScheduleInitial.value p.variant s o hm lm,FIz_ScheduleAbsorption.value p.variant s o hm lm]
  rfl
#print axioms value
end AspisR1.FIz_ScheduleFamily
end
