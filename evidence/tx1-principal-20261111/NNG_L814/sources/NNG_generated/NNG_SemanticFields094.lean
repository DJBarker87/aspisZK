import NNG_FinishFields094
import NNG_ReturnedPath137
import NNG_FinishReturn137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SemanticFields094
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport
/-- Transport through the actual observed-semantic call, preserving the
SAME successful finish rather than selecting a second semantic producer. -/
theorem returned (env : RSL.Env) (s : NNG_Context137.Parent Unit)
 (out : r1_semantic.Verified Unit)
 (native : NNG_Context137.emitted (NNG_Context137.calls env) s=.ok (.Ok out)) :
 (∀ q∈(toT11 out).alpha.val,NHS_Fields.QCanonical q) ∧
 (∀ z∈(toT11 out).z.val,NHS_Fields.QCanonical z.x ∧ NHS_Fields.QCanonical z.y) := by
 obtain ⟨p,t,ch,after,_,_,_,finish⟩ := NNG_ReturnedPath137.returned env s out native
 have actual := NNG_FinishReturn137.returned env s.digest s.publicValue p after ch s.observer out finish
 have facts := NNG_FinishFields094.returned env _ (NNG_Output137.verified out) actual
 simpa only [NNG_Output137.verified,NNG_Transport.fromT11_inverse] using facts
#print axioms returned
end AspisR1.NNG_SemanticFields094
