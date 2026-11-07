import NMX_R3_RegistryOps
import LIB_Deployed
import NND_CarrierInjective
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryIds
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem key_native (k : RSL.B32) : key (LIB_Env.nativeKey k) = k := by
 change LIB_Carriers.b32 (LIB_Env.nativeKey k) = k
 exact LIB_Env.key_roundtrip k

theorem native_unkey (k : RSL.B32) : LIB_Env.nativeKey k = unkey k := by
 apply NND_Carrier.key_injective
 rw [key_native,key_forth]

/-- Install both CLOSED opaque deployment-ID children at their nullary calls.
The same release selector, index error and reservation reach the supplier. -/
theorem pool {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
 (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
 (base : Ops) (env : RSL.Env) :
 (NHJ_DeployedIds.configuration missing devnet indexError reservation).adapter.op45 =
 (NMX_R3_RegistryOps.install base (LIB_Deployed.ids devnet) env).op45 := by
 rw [LIB_Deployed.pool_actual,native_unkey]
 rfl

theorem registry {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
 (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation)
 (base : Ops) (env : RSL.Env) :
 (NHJ_DeployedIds.configuration missing devnet indexError reservation).adapter.op46 =
 (NMX_R3_RegistryOps.install base (LIB_Deployed.ids devnet) env).op46 := by
 rw [LIB_Deployed.registry_actual,native_unkey]
 rfl
#print axioms key_native
#print axioms native_unkey
#print axioms pool
#print axioms registry
end NMX_R3_RegistryIds
end
