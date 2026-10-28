import NCX_ZeroLaws
set_option autoImplicit false
namespace NCX_ParsedBodies
open Aeneas Aeneas.Std Result AspisR1

def validation {A : Type} (v : A) : core.result.Result Unit NCX_Reference.PoolV1VerifierRegistryFormatError →
    core.result.Result A NCX_Reference.PoolV1VerifierRegistryFormatError
  | .Ok () => .Ok v
  | .Err e => .Err e

/-- Parser assembly with every observed field explicit; no validation-success premise. -/
theorem registry (b : Slice U8) (v : NCX_Reference.VerifierRegistryV2)
    (size : Slice.len b=256#usize)
    (magic : NCX_Reference.magic b NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true)
    (version : Slice.index_usize b 4#usize=ok 3#u8)
    (mode : Slice.index_usize b 6#usize=ok 1#u8)
    (zeros : NCX_Reference.zero (JHg_FieldRead.segment b 249 7)=ok true)
    (read_flags : Slice.index_usize b 5#usize=ok v.flags)
    (read_bump : Slice.index_usize b 7#usize=ok v.bump)
    (read_pool : NCX_Reference.read32 b 8#usize=ok v.pool)
    (read_authority : NCX_Reference.read32 b 40#usize=ok v.authority)
    (read_policy_binding : NCX_Reference.read32 b 72#usize=ok v.policy_binding)
    (read_generation : NCX_Reference.word b 104#usize=ok v.generation)
    (read_minimum_activation_delay_slots : NCX_Reference.word b 112#usize=ok v.minimum_activation_delay_slots)
    (read_registry_program : NCX_Reference.read32 b 120#usize=ok v.registry_program)
    (read_loader_program : NCX_Reference.read32 b 152#usize=ok v.loader_program)
    (read_programdata_address : NCX_Reference.read32 b 184#usize=ok v.programdata_address)
    (read_programdata_bump : Slice.index_usize b 248#usize=ok v.programdata_bump)
    (read_executable_hash : NCX_Reference.read32 b 216#usize=ok v.executable_hash)
    : NCX_Reference.decode_verifier_registry_v2 b=
      (do let r ← NCX_Reference.validate_verifier_registry_v2 v;ok (validation v r)) := by
  have length : b.val.length=256 := congrArg UScalar.val size
  have reserved:=JHg_FieldRead.read b 249#usize 256#usize (by scalar_tac) (by scalar_tac)
  simp only [NCX_Reference.decode_verifier_registry_v2,size,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_BYTES,
    NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,version,mode,reserved,zeros,
    read_flags,read_bump,read_pool,read_authority,read_policy_binding,read_generation,read_minimum_activation_delay_slots,read_registry_program,read_loader_program,read_programdata_address,read_programdata_bump,read_executable_hash,
    bind_tc_ok,show (256#usize != 256#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,show (249#usize).val=249 from rfl,
    show (256#usize).val=256 from rfl,Nat.reduceSub,
    bind_tc_ok]
  cases h : NCX_Reference.validate_verifier_registry_v2 v with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok r => cases r <;> rfl
#print axioms registry

/-- Parser assembly with every observed field explicit; no validation-success premise. -/
theorem entry (b : Slice U8) (v : NCX_Reference.VerifierRegistryEntryV2)
    (size : Slice.len b=320#usize)
    (magic : NCX_Reference.magic b NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC=ok true)
    (version : Slice.index_usize b 4#usize=ok 3#u8)
    (mode : Slice.index_usize b 7#usize=ok 1#u8)
    (zeros : NCX_Reference.zero (JHg_FieldRead.segment b 314 6)=ok true)
    (st : U8) (status_byte : Slice.index_usize b 5#usize=ok st)
    (status : NCX_Reference.status st=ok (.Ok v.status))
    (read_statement_version : Slice.index_usize b 6#usize=ok v.statement_version)
    (read_bump : Slice.index_usize b 312#usize=ok v.bump)
    (read_pool : NCX_Reference.read32 b 8#usize=ok v.pool)
    (read_verifier_program : NCX_Reference.read32 b 40#usize=ok v.verifier_program)
    (read_profile_binding : NCX_Reference.read32 b 72#usize=ok v.profile_binding)
    (read_release_binding : NCX_Reference.read32 b 104#usize=ok v.release_binding)
    (read_loader_program : NCX_Reference.read32 b 136#usize=ok v.loader_program)
    (read_programdata_address : NCX_Reference.read32 b 168#usize=ok v.programdata_address)
    (read_programdata_bump : Slice.index_usize b 313#usize=ok v.programdata_bump)
    (read_executable_hash : NCX_Reference.read32 b 200#usize=ok v.executable_hash)
    (read_expected_upgrade_authority : NCX_Reference.read32 b 232#usize=ok v.expected_upgrade_authority)
    (read_activation_slot : NCX_Reference.word b 264#usize=ok v.activation_slot)
    (read_retirement_slot : NCX_Reference.word b 272#usize=ok v.retirement_slot)
    (read_policy_binding : NCX_Reference.read32 b 280#usize=ok v.policy_binding)
    : NCX_Reference.decode_verifier_registry_entry_v2 b=
      (do let r ← NCX_Reference.validate_verifier_registry_entry_v2 v;ok (validation v r)) := by
  have length : b.val.length=320 := congrArg UScalar.val size
  have reserved:=JHg_FieldRead.read b 314#usize 320#usize (by scalar_tac) (by scalar_tac)
  simp only [NCX_Reference.decode_verifier_registry_entry_v2,size,NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_BYTES,
    NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,version,mode,reserved,zeros,
    read_statement_version,read_bump,read_pool,read_verifier_program,read_profile_binding,read_release_binding,read_loader_program,read_programdata_address,read_programdata_bump,read_executable_hash,read_expected_upgrade_authority,read_activation_slot,read_retirement_slot,read_policy_binding,
    bind_tc_ok,show (320#usize != 320#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,show (314#usize).val=314 from rfl,
    show (320#usize).val=320 from rfl,Nat.reduceSub,
    status_byte,status,core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok]
  cases h : NCX_Reference.validate_verifier_registry_entry_v2 v with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok r => cases r <;> rfl
#print axioms entry
end NCX_ParsedBodies
