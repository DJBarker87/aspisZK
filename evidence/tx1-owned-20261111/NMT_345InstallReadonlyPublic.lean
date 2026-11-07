import NMT_345InstallReadonlyProof
import NMT_345BoundaryReadonlyPublic
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

theorem install_readonly_public {W : Type} (c : Calls) (s : Selected W) :
 raw01 (installReadonly c) s =
 if s.publicAccount.is_signer || s.publicAccount.is_writable || s.publicAccount.executable
 then .ok (.Err .InvalidAccountData) else raw02 (installReadonly c) s := by
 rw [boundaryReadonlyPublic]
 change readonlyPublicStep s (raw02 (installReadonly c)) = _
 exact readonlyPublic_closed _ _
#print axioms install_readonly_public
end NMT_345
