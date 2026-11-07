import NND_PoolReturned
import RSL_TX2_234
set_option autoImplicit false
namespace NND_RegistryEval
open RSL RSL.TX2_234 NND_Returned

def pdaValue (env : Env) (seeds : List Bytes) (program : B32) : Except ProgramError B32 :=
 option (env.pda seeds program) .invalidAccountData

def immutableValue (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) : Except ProgramError Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  ebind (id a.registry_account.data) fun rdata =>
  ebind (option (L.decodeRegistryV2 rdata) .invalidAccountData) fun r =>
  ebind (pdaValue env [SEED_REGISTRY_V2, mk, mk1 r.bump] reg) fun expected =>
  eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  ebind (pdaValue env [reg.bytes, mk1 r.programdata_bump] LOADER_ID) fun rpd =>
  eseq (echeck (registryV2Bad D a r rpd) .invalidAccountData) <|
  eseq (id (readonlyAccount a.entry_account reg)) <|
  ebind (id a.entry_account.data) fun edata =>
  ebind (option (L.decodeEntryV2 edata) .invalidAccountData) fun e =>
  ebind (pdaValue env [SEED_ENTRY_V2, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  eseq (echeck (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  ebind (pdaValue env [a.verifier_program.bytes, mk1 e.programdata_bump] LOADER_ID) fun vpd =>
  eseq (echeck (entryV2Bad a e vpd) .invalidAccountData) <|
  Except.ok ()

def v1Value (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) : Except ProgramError Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  ebind (id a.registry_account.data) fun rdata =>
  ebind (option (L.decodeRegistryV1 rdata) .invalidAccountData) fun r =>
  ebind (pdaValue env [SEED_REGISTRY, mk, mk1 r.bump] reg) fun expected =>
  eseq (echeck (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  eseq (echeck (registryV1Bad a r) .invalidAccountData) <|
  eseq (id (readonlyAccount a.entry_account reg)) <|
  ebind (id a.entry_account.data) fun edata =>
  ebind (option (L.decodeEntryV1 edata) .invalidAccountData) fun e =>
  ebind (pdaValue env [SEED_ENTRY, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  eseq (echeck (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  eseq (echeck (entryV1Bad a e) .invalidAccountData) <|
  Except.ok ()

def value (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) : Except ProgramError Unit :=
  eseq (echeck (policyBad D a) .invalidAccountData) <|
  eseq (echeck (!L.validatePolicy a.master.verifier_policy) .invalidAccountData) <|
  eseq (id (readonlyAccount a.registry_account D.registry)) <|
  if a.master.verifier_policy.flags &&& POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0 then
    immutableValue L D a env
  else
    v1Value L D a env

syntax "registry_steps " term : tactic
macro_rules
| `(tactic| registry_steps $env:term) => `(tactic|
 first
 | exact NND_Returned.ofExcept $env _
 | exact NND_Returned.ofOption $env _ _
 | exact NND_Returned.pdaOrErr $env _ _
 | exact NND_Returned.check $env _ _
 | exact NND_Returned.rs_pure $env _
 | (apply NND_Returned.seq <;> registry_steps $env)
 | (apply NND_Returned.rs_bind <;> registry_steps $env)
 | (intro; registry_steps $env))

theorem immutable_returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (immutableBranch L D a) env (immutableValue L D a env) := by
 unfold immutableBranch immutableValue
 registry_steps env

theorem v1_returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (v1Branch L D a) env (v1Value L D a env) := by
 unfold v1Branch v1Value
 registry_steps env

theorem returned (L : PoolLib) (D : DeployedIds) (a : Args) (env : Env) :
 Returns (Ref L D a) env (value L D a env) := by
 unfold Ref value
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (check env _ _)
 apply seq _ _ env _ _ (ofExcept env _)
 split
 · exact immutable_returned L D a env
 · exact v1_returned L D a env

#print axioms immutable_returned
#print axioms v1_returned
#print axioms returned
end NND_RegistryEval
