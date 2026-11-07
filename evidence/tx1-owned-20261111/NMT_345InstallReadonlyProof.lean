import NMT_345BoundaryReadonlyProof
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def installReadonly (c : Calls) : Calls := {c with c13 := readonlyCall}
theorem install_readonly_proof {W : Type} (c : Calls) (s : Selected W) :
 raw00 (installReadonly c) s =
 if s.proofAccount.is_signer || s.proofAccount.is_writable || s.proofAccount.executable
 then .ok (.Err .InvalidAccountData) else raw01 (installReadonly c) s := by
 rw [boundaryReadonlyProof]
 change readonlyProofStep s (raw01 (installReadonly c)) = _
 exact readonlyProof_closed _ _
#print axioms install_readonly_proof
end NMT_345
