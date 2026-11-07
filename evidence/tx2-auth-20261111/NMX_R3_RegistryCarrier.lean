import NND_Carrier
import RSL_Pool
set_option autoImplicit false
namespace NMX_R3_RegistryCarrier
open Aeneas Aeneas.Std AdapterRw NND_Carrier
/-- Same complete owned input; data remains a cloned-error computation when
read by the reference. This definition does not install a getter law. -/
def account (a : r1_pool_adapter.owned.OwnedAccount) : RSL.OwnedAccount :=
 ⟨key a.key,key a.owner,a.is_signer,a.is_writable,a.executable,
  reply (fun n : Usize => n.val) a.length,reply bytes a.bytes⟩
end NMX_R3_RegistryCarrier
