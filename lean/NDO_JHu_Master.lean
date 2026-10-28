import NDO_JHu_MasterIdentity
import NDO_JHu_MasterValid
import JHu_FixtureSequences
import NCV_Install
set_option autoImplicit false
namespace AspisR1.JHu_Master
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataMaster.bytes

theorem source : NCV_Reference.decode_master_ref JHg_DataMaster.value=
    ok (.Ok (NCV_Carrier.fromMaster JHg_AccountValues.master)) := by
  have len : JHg_DataMaster.value.val.length=384 := JHg_DataMaster.length
  have size : Slice.len JHg_DataMaster.value=384#usize := UScalar.eq_of_val_eq len
  have start:=NCV_FieldViews.read_prefix JHg_DataMaster.value 4#usize (by scalar_tac)
  have magic : NCV_Reference.equal (JHg_FieldRead.segment JHg_DataMaster.value 0 4)
      (Array.make 4#usize [65#u8,83#u8,77#u8,56#u8]).to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · exact JHg_AuditMaster.magic
  have version : Slice.index_usize JHg_DataMaster.value 4#usize=ok 2#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.version
  have lanes : Slice.index_usize JHg_DataMaster.value 5#usize=ok 8#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.lanes
  have encoding : Slice.index_usize JHg_DataMaster.value 6#usize=ok 1#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.encoding
  have reserved0:=JHg_FieldRead.read JHg_DataMaster.value 50#usize 64#usize (by scalar_tac) (by scalar_tac)
  have zero0 : NCV_Reference.zero (JHg_FieldRead.segment JHg_DataMaster.value 50 14)=ok true :=
    JHu_ZeroFields.zero _ 14 JHg_AuditMaster.reserved0 (by omega)
  have reserved1:=JHg_FieldRead.read JHg_DataMaster.value 312#usize 320#usize (by scalar_tac) (by scalar_tac)
  have zero1 : NCV_Reference.zero (JHg_FieldRead.segment JHg_DataMaster.value 312 8)=ok true :=
    JHu_ZeroFields.zero _ 8 JHg_AuditMaster.reserved1 (by omega)
  have bindingRead:=JHg_FieldRead.read JHg_DataMaster.value 8#usize 40#usize (by scalar_tac) (by scalar_tac)
  have binding : NCV_Reference.equal (JHg_FieldRead.segment JHg_DataMaster.value 8 32)
      NCV_Reference.BINDING.to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 8 32 (by omega)];omega
    · unfold NCV_Reference.BINDING
      exact JHg_AuditMaster.format
  have has : Slice.index_usize JHg_DataMaster.value 49#usize=ok 1#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.has_checkpoint
  have identityRead:=JHg_FieldRead.read JHg_DataMaster.value 64#usize 208#usize (by scalar_tac) (by scalar_tac)
  have policyRead:=JHg_FieldRead.read JHg_DataMaster.value 208#usize 312#usize (by scalar_tac) (by scalar_tac)
  have bump : Slice.index_usize JHg_DataMaster.value 7#usize=ok 254#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.bump
  have mask : Slice.index_usize JHg_DataMaster.value 48#usize=ok 255#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditMaster.lane_mask
  have counter : NCV_Reference.word64 JHg_DataMaster.value 40#usize=
      ok (core.num.U64.from_le_bytes JHg_Scalar00.value) :=
    JHu_ReferenceWords.word64 _ _ _ (by omega) (by scalar_tac) JHg_Scalar00.bytes
  have identity : NCV_Reference.identity (JHg_FieldRead.segment JHg_DataMaster.value 64 144)=
      ok (.Ok (NCV_Carrier.fromIdentity JHg_AccountValues.master.identity)) := JHu_MasterIdentity.source
  have policy : NCV_Reference.policy (JHg_FieldRead.segment JHg_DataMaster.value 208 104)=
      ok (.Ok (NCV_Carrier.fromPolicy JHg_AccountValues.master.verifier_policy)) := JHu_MasterPolicy.source
  have valid : NCV_Reference.valid_master
      ⟨254#u8,NCV_Carrier.fromIdentity JHg_AccountValues.master.identity,
       NCV_Carrier.fromPolicy JHg_AccountValues.master.verifier_policy,255#u8,true,
       core.num.U64.from_le_bytes JHg_Scalar00.value,Array.repeat 8#usize 0#u64⟩=ok true := JHu_MasterValid.source
  simp only [NCV_Reference.decode_master_ref,size,show (384#usize != 384#usize)=false from rfl,
    Bool.false_eq_true,ite_false,start,lift,bind_tc_ok,
    show (4#usize).val=4 from rfl,show (50#usize).val=50 from rfl,
    show (64#usize).val=64 from rfl,show (312#usize).val=312 from rfl,
    show (320#usize).val=320 from rfl,show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,show (208#usize).val=208 from rfl,
    Nat.reduceSub,magic,ite_true,version,lanes,encoding,
    show (2#u8 != 2#u8)=false from rfl,show (8#u8 != 8#u8)=false from rfl,
    show (1#u8 != 1#u8)=false from rfl,reserved0,zero0,reserved1,zero1,
    bindingRead,binding,has,identityRead,identity,policyRead,policy,
    core.result.Result.Insts.CoreOpsTry.branch,JHu_FixtureSequences.master,bump,mask,counter,valid]
  rfl
#print axioms source

theorem observation : NCV_Install.op48 JHg_DataMaster.value=ok (.Ok JHg_AccountValues.master) := by
  simp only [NCV_Install.op48,source,bind_tc_ok,NCV_Install.mapReturn,NCV_Carrier.master_surjective]
#print axioms observation
end AspisR1.JHu_Master
