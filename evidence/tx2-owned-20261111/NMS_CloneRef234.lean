import RSL_TX2_234
import NMS_GeneralGetters
set_option autoImplicit false
namespace NMS_CloneRef234
open RSL RSL.TX2_234

/- Canonical RSL reference with explicit general ProgramError clone stops.
Only getter interpretation and recursively corrected child references differ.
No normal result, payload, ordered effect, Box or original input is erased. -/
/-- Immutable-deployment branch, lines 107-175, in source order. -/
def immutableBranch (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  RS.bind (NMS_GeneralGetters.data a.registry_account) fun rdata =>
  RS.bind (RS.ofOption (L.decodeRegistryV2 rdata) .invalidAccountData) fun r =>
  RS.bind (pdaOrErr [SEED_REGISTRY_V2, mk, mk1 r.bump] reg) fun expected =>
  RS.seq (RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  RS.bind (pdaOrErr [reg.bytes, mk1 r.programdata_bump] LOADER_ID) fun rpd =>
  RS.seq (RS.check (registryV2Bad D a r rpd) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.entry_account reg)) <|
  RS.bind (NMS_GeneralGetters.data a.entry_account) fun edata =>
  RS.bind (RS.ofOption (L.decodeEntryV2 edata) .invalidAccountData) fun e =>
  RS.bind (pdaOrErr [SEED_ENTRY_V2, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  RS.seq (RS.check (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  RS.bind (pdaOrErr [a.verifier_program.bytes, mk1 e.programdata_bump] LOADER_ID) fun vpd =>
  RS.seq (RS.check (entryV2Bad a e vpd) .invalidAccountData) <|
  RS.pure ()

/-- V1 branch, lines 177-226, in source order. -/
def v1Branch (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  RS.bind (NMS_GeneralGetters.data a.registry_account) fun rdata =>
  RS.bind (RS.ofOption (L.decodeRegistryV1 rdata) .invalidAccountData) fun r =>
  RS.bind (pdaOrErr [SEED_REGISTRY, mk, mk1 r.bump] reg) fun expected =>
  RS.seq (RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  RS.seq (RS.check (registryV1Bad a r) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.entry_account reg)) <|
  RS.bind (NMS_GeneralGetters.data a.entry_account) fun edata =>
  RS.bind (RS.ofOption (L.decodeEntryV1 edata) .invalidAccountData) fun e =>
  RS.bind (pdaOrErr [SEED_ENTRY, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  RS.seq (RS.check (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  RS.seq (RS.check (entryV1Bad a e) .invalidAccountData) <|
  RS.pure ()

/-- Reference: the complete body. -/
def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  RS.seq (RS.check (policyBad D a) .invalidAccountData) <|
  RS.seq (RS.check (!L.validatePolicy a.master.verifier_policy) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.registry_account D.registry)) <|
  if a.master.verifier_policy.flags &&& POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0 then
    immutableBranch L D a
  else
    v1Branch L D a


end NMS_CloneRef234
