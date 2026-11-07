import NLZ_PrepareOwnDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_PrepareDomainTransport
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Only the own-input portion of179's domain is discharged here. Neither
Opening/query/rho packets nor physical owner/lifetime admission follows. -/
theorem compact (i : NLJ_Prepare.Input Unit) (own : NLZ_PrepareOwnDomain.Domain i) :
 (NLZ_PrepareOwnDomain.compact i).val.length=464 ∧
 NFU_Retarget.compact.check_values (NLZ_PrepareOwnDomain.compact i)=ok (.Ok ()) :=
 ⟨NLZ_PrepareOwnDomain.compact_width i own.proofLength,own.compactCanonical⟩
/-- Domain transport uses actual input equality, not an independent caller
success. Native087 still has to prove this equality on each entered segment. -/
theorem transport (i j : NLJ_Prepare.Input Unit) (same : j=i)
 (own : NLZ_PrepareOwnDomain.Domain i) : NLZ_PrepareOwnDomain.Domain j := by
 rw [same]
 exact own
#print axioms compact
#print axioms transport
#print compact
end AspisR1.NLZ_PrepareDomainTransport
end
