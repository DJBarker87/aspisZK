import NND_RegistryOps
import NND_V2DecoderValues
set_option autoImplicit false
noncomputable section
namespace NND_RegistryLibrary
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier

def install (base : RSL.PoolLib) : RSL.PoolLib :=
 {base with
  validatePolicy := NND_PolicyValue.validate
  decodeRegistryV1 := NND_V1DecoderValues.registry
  decodeRegistryV2 := NND_V2DecoderValues.registry
  decodeEntryV1 := NND_V1DecoderValues.entry
  decodeEntryV2 := NND_V2DecoderValues.entry}

theorem registry1 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NND_V1DecoderValues.asOption registryV1) ((NND_RegistryOps.install base D env).op31 b) =
 ok ((install L).decodeRegistryV1 (bytes b)) := NND_V1DecoderValues.registry_result b

theorem entry1 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NND_V1DecoderValues.asOption entryV1) ((NND_RegistryOps.install base D env).op32 b) =
 ok ((install L).decodeEntryV1 (bytes b)) := NND_V1DecoderValues.entry_result b

theorem registry2 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NND_V1DecoderValues.asOption registryV2) ((NND_RegistryOps.install base D env).op33 b) =
 ok ((install L).decodeRegistryV2 (bytes b)) := NND_V2DecoderValues.registry_result b

theorem entry2 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NND_V1DecoderValues.asOption entryV2) ((NND_RegistryOps.install base D env).op34 b) =
 ok ((install L).decodeEntryV2 (bytes b)) := NND_V2DecoderValues.entry_result b

theorem policy (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :
 outer NND_PolicyValue.isOk ((NND_RegistryOps.install base D env).op15 p) =
 ok ((install L).validatePolicy (NND_Carrier.policy p)) := NND_PolicyValue.native p

#print axioms registry1
#print axioms entry1
#print axioms registry2
#print axioms entry2
#print axioms policy
end NND_RegistryLibrary
end
