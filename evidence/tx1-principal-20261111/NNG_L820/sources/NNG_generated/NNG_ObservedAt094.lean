import NNG_SemanticAt094
import NNG_ReturnedPath137
import NNG_FinishReturn137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ObservedAt094
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
/-- The observed wrapper transports its actual finish with the SAME supplied
environment digest; reservation is an internal earlier-return fact. -/
theorem returned (env : RSL.Env) (s : NNG_Context137.Parent Unit)
 (out : r1_semantic.Verified Unit)
 (native : NNG_Context137.emitted (NNG_Context137.calls env) s=.ok (.Ok out))
 (digest : s.digest=NNG_PublicSource137.digest env) (reserved : env.reservation=true) :
 NNG_SemanticAt094.SemanticAt env (toT11 out) := by
 obtain ⟨p,t,ch,after,_,_,_,finish⟩ := NNG_ReturnedPath137.returned env s out native
 have actual := NNG_FinishReturn137.returned env s.digest s.publicValue p after ch s.observer out finish
 have digestEq : (NNG_FinishAdapter137.childInput s.digest (toT9 s.publicValue)
  (toT13 p) (toT10 after) (toT3 ch) s.observer).digest=NNG_LIBDigest.digest env := by
  rw [digest]
  rfl
 have same := NNG_SemanticAt094.finish env _ (NNG_Output137.verified out) actual digestEq reserved
 simpa only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] using same
#print axioms returned
end AspisR1.NNG_ObservedAt094
