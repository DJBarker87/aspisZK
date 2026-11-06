import NLH_PartsValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsStep5
open Aeneas Aeneas.Std Result FIq_Native NLH_PartsValues
open NKR_TermTail (Calls Carrier)
theorem call (zc point : Array FIv_NativeArithmetic.NQ 10#usize) (mu : FIv_NativeArithmetic.NQ)
 (child : Carrier) (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) :
 NLH_PartsState.arithmetic zc point mu (stage child p 5) 5=ok (values p 5) := by
 exact p.inactive_call
#print axioms call
end AspisR1.NLH_PartsStep5
end
