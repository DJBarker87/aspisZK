import NDO_JHu_WindowFields
import NDO_JHg_AccountValues
import NCV_Carrier
set_option autoImplicit false
namespace AspisR1.JHu_MasterIdentity
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataMaster.bytes

def window : Slice U8 := JHg_FieldRead.segment JHg_DataMaster.value 64 144

theorem source : NCV_Reference.identity window=
    ok (.Ok (NCV_Carrier.fromIdentity JHg_AccountValues.master.identity)) := by
  have len : JHg_DataMaster.value.val.length=384 := JHg_DataMaster.length
  have wl : window.val.length=144 := JHg_FieldRead.length _ _ _ (by omega)
  have size : Slice.len window=144#usize := UScalar.eq_of_val_eq wl
  have start:=NCV_FieldViews.read_prefix window 4#usize (by scalar_tac)
  have magic : NCV_Reference.equal (JHg_FieldRead.segment window 0 4)
      (Array.make 4#usize [65#u8,83#u8,80#u8,73#u8]).to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · change (JHg_FieldRead.segment window 0 4).val=_
      rw [show window=JHg_FieldRead.segment JHg_DataMaster.value 64 144 from rfl,
        NCV_FieldViews.nested _ 64 144 0 4 (by omega)]
      exact JHg_AuditMaster.identity_magic
  have version : Slice.index_usize window 4#usize=ok 1#u8 :=
    JHu_WindowFields.byte _ 64 144 _ _ (by omega) (by scalar_tac) JHg_AuditMaster.identity_version
  have reserved0:=JHg_FieldRead.read window 5#usize 8#usize (by scalar_tac) (by scalar_tac)
  have zero0 : NCV_Reference.zero (JHg_FieldRead.segment window 5 3)=ok true := by
    apply JHu_ZeroFields.zero _ 3 _ (by omega)
    change ((JHg_FieldRead.segment JHg_DataMaster.value 64 144).val.drop 5).take 3=_
    rw [JHu_WindowFields.field _ 64 144 5 3 (by omega)]
    exact JHg_AuditMaster.identity_reserved
  have reserved1:=JHg_FieldRead.read window 108#usize 112#usize (by scalar_tac) (by scalar_tac)
  have zero1 : NCV_Reference.zero (JHg_FieldRead.segment window 108 4)=ok true := by
    apply JHu_ZeroFields.zero _ 4 _ (by omega)
    change ((JHg_FieldRead.segment JHg_DataMaster.value 64 144).val.drop 108).take 4=_
    rw [JHu_WindowFields.field _ 64 144 108 4 (by omega)]
    exact JHg_AuditMaster.identity_reserved1
  let asset : Array U8 4#usize := Array.make 4#usize [77#u8,0#u8,0#u8,0#u8]
  have readAsset : NCV_Reference.word32 window 104#usize=ok 77#u32 := by
    have field : (window.val.drop 104).take 4=asset.val := by
      rw [show window=JHg_FieldRead.segment JHg_DataMaster.value 64 144 from rfl,
        JHu_WindowFields.field _ 64 144 104 4 (by omega)]
      exact JHg_AuditMaster.asset
    exact JHu_ReferenceWords.word32 window 104#usize asset (by omega) (by scalar_tac) field
  have pool : NCV_Reference.bytes32 window 8#usize=ok JHg_AccountValues.master.identity.pool :=
    JHu_WindowFields.bytes32 _ 64 144 _ _ (by omega) (by omega) (by scalar_tac) JHg_BindingsMaster.pool
  have mint : NCV_Reference.bytes32 window 40#usize=ok JHg_AccountValues.master.identity.asset_mint :=
    JHu_WindowFields.bytes32 _ 64 144 _ _ (by omega) (by omega) (by scalar_tac) JHg_AuditMaster.mint
  have token : NCV_Reference.bytes32 window 72#usize=ok JHg_AccountValues.master.identity.token_program :=
    JHu_WindowFields.bytes32 _ 64 144 _ _ (by omega) (by omega) (by scalar_tac) (Eq.refl _)
  have domain : NCV_Reference.bytes32 window 112#usize=ok JHg_AccountValues.master.identity.deployment_domain :=
    JHu_WindowFields.bytes32 _ 64 144 _ _ (by omega) (by omega) (by scalar_tac) (Eq.refl _)
  have assetValid : ¬(77#u32 : U32) >= 2147483647#u32 := by scalar_tac
  simp only [NCV_Reference.identity,size,show (144#usize != 144#usize)=false from rfl,
    Bool.false_eq_true,ite_false,show (4#usize).val=4 from rfl,show (5#usize).val=5 from rfl,show (8#usize).val=8 from rfl,show (108#usize).val=108 from rfl,show (112#usize).val=112 from rfl,Nat.reduceSub,start,lift,bind_tc_ok,magic,ite_true,version,
    show (1#u8 != 1#u8)=false from rfl,reserved0,zero0,reserved1,zero1,
    readAsset,assetValid,pool,mint,token,domain]
  rfl
#print axioms source
end AspisR1.JHu_MasterIdentity
