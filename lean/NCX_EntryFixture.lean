import NCX_EntryValue
import NCX_Status
set_option autoImplicit false
namespace NCX_EntryFixture
open Aeneas Aeneas.Std Result AspisR1
open NCX_EntryFields
attribute [local irreducible] JHb_DataEntry.bytes

theorem source : NCX_Reference.decode_verifier_registry_entry_v2 JHb_DataEntry.value=
    ok (.Ok NCX_EntryValue.value) := by
  have len : JHb_DataEntry.value.val.length=320 := JHb_DataEntry.length
  have size : Slice.len JHb_DataEntry.value=320#usize := UScalar.eq_of_val_eq len
  have magic : NCX_Reference.magic JHb_DataEntry.value NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC=ok true := by
    apply NCX_ZeroLaws.magic
    · omega
    · simpa only [JHb_DataEntry.value,Array.make,List.drop_zero,NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_MAGIC] using JHg_AuditEntry.magic
  have reserved:=JHg_FieldRead.read JHb_DataEntry.value 314#usize 320#usize (by scalar_tac) (by scalar_tac)
  have zeros : NCX_Reference.zero (JHg_FieldRead.segment JHb_DataEntry.value 314 6)=ok true :=
    NCX_ZeroLaws.zero _ 6 JHg_AuditEntry.reserved (by omega)
  have valid:=NCX_EntryValue.valid
  unfold NCX_EntryValue.value at valid
  simp only [NCX_Reference.decode_verifier_registry_entry_v2,size,NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_BYTES,
    NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_VERSION,NCX_Reference.POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3,
    magic,reserved,zeros,
    read_version,read_status,read_statement_version,read_mode,read_pool,read_verifier,read_profile,read_release,read_loader,read_programdata,read_executable_hash,read_upgrade_authority,read_activation,read_retirement,read_policy,read_bump,read_programdata_bump,
    bind_tc_ok,show (320#usize != 320#usize)=false from rfl,
    show (3#u8 != 3#u8)=false from rfl,show (1#u8 != 1#u8)=false from rfl,
    Bool.false_eq_true,ite_false,ite_true,
    show (314#usize).val=314 from rfl,show (320#usize).val=320 from rfl,Nat.reduceSub,
    NCX_Status.active,core.result.Result.Insts.CoreOpsTry.branch,
    valid,core.result.Result.Insts.CoreOpsTry.branch]
  rfl
#print axioms source
end NCX_EntryFixture
