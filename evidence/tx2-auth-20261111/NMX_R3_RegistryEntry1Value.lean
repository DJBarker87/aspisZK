import NMX_R3_RegistryEntry1Check
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEntry1Value
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1)
 (expected : solana_pubkey.Pubkey) :
 NMX_R3_RegistryEntry1Check.check (NMX_R3_RegistryOps.install base D env) v m.key e t entry expected =
 ok (if !decide (e.key = expected) || NMX_R3_EntryRecordGuards.bad1 v m entry t
     then .Err .InvalidAccountData else .Ok ()) := by
 simp only [NMX_R3_RegistryEntry1Check.check, NMX_R3_RegistryNativeParts.native018,NMX_R3_RegistryStd.key_ne,
  NMX_R3_RegistryScalarOps.to_bytes,NMX_R3_RegistryScalarOps.version,NMX_R3_RegistryScalarOps.active1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
  NMX_R3_EntryRecordGuards.bad1,NND_BoolReject.not_guard]
 exact (NND_BoolReject.eight _ _ _ _ _ _ _ _ _ _).trans (by split <;> rfl)

#print axioms value
end NMX_R3_RegistryEntry1Value
end
