import FIw_SelectedValue
import FIw_CompositionOrigins
import FJn_H1Origin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_SelectedValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode)
/-- SAME actual H1 read; no independently supplied helper value. -/
theorem helper (pub : FIw_CompositionOrigins.SemPub) (claims : Array field.QM31 84#usize)
    (point : Array field.QM31 10#usize) (lambda chi theta comp g h active : field.QM31)
    (c1 : Array field.QM31 16#usize) (mask : Array field.QM31 10#usize)
    (run : FIw_CompositionOrigins.composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    decode h=FIv_NativeArray.value claims 26 := by
  have called:=FJn_H1Origin.reached pub claims point lambda chi theta comp g h active c1 mask run
  have v:=FIw_SelectedValue.value claims 0#usize 26#usize h called
  change decode h=FIv_NativeArray.value claims (0*28+26) at v
  simpa only [Nat.zero_mul,Nat.zero_add] using v
#print axioms helper
end AspisR1.FJn_SelectedValue
end
