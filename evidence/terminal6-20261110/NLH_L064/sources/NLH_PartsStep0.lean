import NLH_PartsValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_PartsStep0
open Aeneas Aeneas.Std Result FIq_Native NLH_PartsValues
open NKR_TermTail (Calls Carrier)
theorem call (zc point : Array FIv_NativeArithmetic.NQ 10#usize) (mu : FIv_NativeArithmetic.NQ)
 (child : Carrier) (p : Calls zc point mu child.1 child.2.2.2.2.1 child.2.2.2.2.2) :
 NLH_PartsState.arithmetic zc point mu (stage child p 0) 0=ok (values p 0) := by
 exact p.equality
#print axioms call
end AspisR1.NLH_PartsStep0
end
