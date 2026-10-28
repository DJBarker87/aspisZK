import NCX_RegistryValue
set_option autoImplicit false
namespace NCX_RegistryFixture
open Aeneas Aeneas.Std Result AspisR1
open NCX_RegistryFields
attribute [local irreducible] JHb_DataRegistry.bytes

theorem source : NCX_Reference.decode_verifier_registry_v2 JHb_DataRegistry.value=
    ok (.Ok NCX_RegistryValue.value) := by
  have len : JHb_DataRegistry.value.val.length=256 := JHb_DataRegistry.length
  have size : Slice.len JHb_DataRegistry.value=256#usize := UScalar.eq_of_val_eq len
  have magic : NCX_Reference.magic JHb_DataRegistry.value NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC=ok true := by
    apply NCX_ZeroLaws.magic
    · omega
    · simpa only [List.drop_zero,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_MAGIC] using JHg_AuditRegistry.magic
  have reserved:=JHg_FieldRead.read JHb_DataRegistry.value 249#usize 256#usize (by scalar_tac) (by scalar_tac)
  have zeros : NCX_Reference.zero (JHg_FieldRead.segment JHb_DataRegistry.value 249 7)=ok true :=
    NCX_ZeroLaws.zero _ 7 JHg_AuditRegistry.reserved (by omega)
  have valid:=NCX_RegistryValue.valid
  unfold NCX_RegistryValue.value at valid
  simp only [NCX_Reference.decode_verifier_registry_v2,size,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_BYTES,
    NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,reserved,zeros,
    read_version,read_flags,read_mode,read_bump,read_pool,read_authority,read_policy,read_generation,read_delay,read_program,read_loader,read_programdata,read_executable_hash,read_programdata_bump,
    bind_tc_ok,show (256#usize != 256#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,
    show (249#usize).val=249 from rfl,show (256#usize).val=256 from rfl,Nat.reduceSub,
    valid,core.result.Result.Insts.CoreOpsTry.branch]
  rfl
#print axioms source
end NCX_RegistryFixture
