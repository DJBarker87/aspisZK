import NND_RegistryStd
set_option autoImplicit false
noncomputable section
namespace NND_RegistryScalarOps
open Aeneas Aeneas.Std Result AdapterRw
variable (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)

theorem to_bytes (p : solana_pubkey.Pubkey) :
 (NND_RegistryOps.install base D env).op39 p = ok p := rfl
theorem as_ref (p : solana_pubkey.Pubkey) :
 (NND_RegistryOps.install base D env).op40 p = ok (Array.to_slice p) := rfl
theorem from_bytes (p : Array U8 32#usize) :
 (NND_RegistryOps.install base D env).op37 p = ok p := rfl
theorem version : (NND_RegistryOps.install base D env).op18 = ok 1#u8 := rfl
theorem immutable_flag : (NND_RegistryOps.install base D env).op13 = ok 1#u8 := rfl
theorem deployment_flag : (NND_RegistryOps.install base D env).op14 = ok 2#u8 := rfl
theorem pool : (NND_RegistryOps.install base D env).op45 = ok (NND_Carrier.unkey D.pool) := rfl
theorem registry : (NND_RegistryOps.install base D env).op46 = ok (NND_Carrier.unkey D.registry) := rfl
theorem loader : (NND_RegistryOps.install base D env).op41 = ok (NND_Carrier.unkey RSL.LOADER_ID) := rfl
theorem active1 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) (t : U64) :
 (NND_RegistryOps.install base D env).op30 r t =
 ok (NIJ_ActiveSlots.active r.status r.activation_slot r.retirement_slot t) := rfl
theorem active2 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (t : U64) :
 (NND_RegistryOps.install base D env).op29 r t =
 ok (NIJ_ActiveSlots.active r.status r.activation_slot r.retirement_slot t) := rfl

#print axioms to_bytes
#print axioms as_ref
#print axioms from_bytes
#print axioms version
#print axioms immutable_flag
#print axioms deployment_flag
#print axioms pool
#print axioms registry
#print axioms loader
#print axioms active1
#print axioms active2
end NND_RegistryScalarOps
end
