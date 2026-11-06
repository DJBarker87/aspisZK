import NLH_PartsValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsStep6
open Aeneas Aeneas.Std Result FIq_Native NLH_PartsValues
open NKR_TermTail (Calls Carrier)
theorem call (zc point : Array FIv_NativeArithmetic.NQ 10#usize) (mu : FIv_NativeArithmetic.NQ)
 (child : Carrier) (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) :
 NLH_PartsState.arithmetic zc point mu (stage child p 6) 6=ok (values p 6) := by
 exact p.inactive_h
#print axioms call
end AspisR1.NLH_PartsStep6
end
