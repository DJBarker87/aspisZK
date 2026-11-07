import NND_CompareTransport
import NND_AccountCarrier
set_option autoImplicit false
noncomputable section
namespace NND_ReadonlyPredicate
open Aeneas Aeneas.Std AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 RSL.readonlyAccount (account a) (key p) =
 if !decide (a.owner = p) || a.is_signer || a.is_writable || a.executable
 then .error .invalidAccountData else .ok () := by
 change (if decide (key a.owner ≠ key p) || a.is_signer || a.is_writable || a.executable then _ else _) = _
 rw [←NND_CompareTransport.key_ne]

#print axioms value
end NND_ReadonlyPredicate
end
