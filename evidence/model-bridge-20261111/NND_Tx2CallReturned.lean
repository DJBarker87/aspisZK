import NND_Tx2Values
set_option autoImplicit false
namespace NND_Tx2Values
open RSL NND_Returned RSL.TX2_241
/-- Dom064 is recovered only from this call's admitted RSL observation. -/
theorem call_returned (V : V2Lib) (w : Values V) (p q r : Bytes) (env : Env) :
 Returns (RS.lift (Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2) (p,q,r)))
 env (.ok (w.auth p q r env)) := by
 apply rs_lift
 apply call_domain
 intro hd
 exact w.auth_ret p q r env hd
#print axioms call_returned
end NND_Tx2Values
