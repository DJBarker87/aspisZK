import XSe_HybridCanonical
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_PowerDomain
/-- Exact four-limb domain consumed by the existing emitted push theorem. -/
theorem source (q : aspis_core.field.QM31) (canonical : XRp_PowersQAdd.CanonicalQ q) :
 ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (XRu_PushTransport.power q) k).val<2^31-1 := by
 intro k
 rcases canonical with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
 fin_cases k
 · exact ha
 · exact hb
 · exact hc
 · exact hd
#print axioms source
end XSe_PowerDomain
