import NMT_345ReadonlyProof
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ReadonlyObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData

theorem law (a : Account) (env : Env) :
 RS.ofExcept (readonlyBuffer (account a)) env (observe id (readonlyCall a)) := by
 rw [readonly_closed]
 unfold readonlyBuffer account
 cases a.is_signer <;> cases a.is_writable <;> cases a.executable <;> rfl
#print axioms law
end NMT_R2_ReadonlyObservation
end
