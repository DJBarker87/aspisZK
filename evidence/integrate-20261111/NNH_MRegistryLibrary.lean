import NNH_MRegistryOps
import NNH_MV2DecoderValues
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryLibrary
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier

def install (base : RSL.PoolLib) : RSL.PoolLib :=
 {base with
  validatePolicy := NNH_MPolicyValue.validate
  decodeRegistryV1 := NNH_MV1DecoderValues.registry
  decodeRegistryV2 := NNH_MV2DecoderValues.registry
  decodeEntryV1 := NNH_MV1DecoderValues.entry
  decodeEntryV2 := NNH_MV2DecoderValues.entry}

theorem registry1 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NNH_MV1DecoderValues.asOption registryV1) ((NNH_MRegistryOps.install base D env).op31 b) =
 ok ((install L).decodeRegistryV1 (bytes b)) := NNH_MV1DecoderValues.registry_result b

theorem entry1 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NNH_MV1DecoderValues.asOption entryV1) ((NNH_MRegistryOps.install base D env).op32 b) =
 ok ((install L).decodeEntryV1 (bytes b)) := NNH_MV1DecoderValues.entry_result b

theorem registry2 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NNH_MV1DecoderValues.asOption registryV2) ((NNH_MRegistryOps.install base D env).op33 b) =
 ok ((install L).decodeRegistryV2 (bytes b)) := NNH_MV2DecoderValues.registry_result b

theorem entry2 (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env) (b : Slice U8) :
 outer (NNH_MV1DecoderValues.asOption entryV2) ((NNH_MRegistryOps.install base D env).op34 b) =
 ok ((install L).decodeEntryV2 (bytes b)) := NNH_MV2DecoderValues.entry_result b

theorem policy (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (p : aspis_statement.pool_v1.format.VerifierPolicyV1) :
 outer NNH_MPolicyValue.isOk ((NNH_MRegistryOps.install base D env).op15 p) =
 ok ((install L).validatePolicy (NND_Carrier.policy p)) := NNH_MPolicyValue.native p

#print axioms registry1
#print axioms entry1
#print axioms registry2
#print axioms entry2
#print axioms policy
end NNH_MRegistryLibrary
end
