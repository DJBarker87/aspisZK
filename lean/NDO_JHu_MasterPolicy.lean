import NDO_JHu_WindowFields
import NDO_JHg_AccountValues
import NCV_Carrier
set_option autoImplicit false
namespace AspisR1.JHu_MasterPolicy
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataMaster.bytes

def window : Slice U8 := JHg_FieldRead.segment JHg_DataMaster.value 208 104

theorem valid : NCV_Reference.valid_policy
    (NCV_Carrier.fromPolicy JHg_AccountValues.master.verifier_policy)=ok true := by
  have registry : NCV_Reference.zero JHb_Programs.registry.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768;omega
    · change (68#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<32;omega
  have binding : NCV_Reference.zero (Array.repeat 32#usize 7#u8).to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768;omega
    · change (7#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<32;omega
  have authority : NCV_Reference.zero (Array.repeat 32#usize 0#u8).to_slice=ok true :=
    JHu_ZeroFields.zero _ 32 (Eq.refl _) (by omega)
  change NCV_Reference.valid_policy
    ⟨3#u8,JHb_Programs.registry,Array.repeat 32#usize 0#u8,Array.repeat 32#usize 7#u8⟩=_
  simp only [NCV_Reference.valid_policy,lift,bind_tc_ok,
    show (3#u8 &&& ~~~3#u8 : U8)=0#u8 from rfl,
    show (0#u8 != 0#u8)=false from rfl,Bool.false_eq_true,ite_false,
    registry,binding,show (3#u8 &&& 1#u8 : U8)=1#u8 from rfl,
    show (3#u8 &&& 2#u8 : U8)=2#u8 from rfl,
    show (1#u8 != 0#u8)=true from rfl,show (2#u8 != 0#u8)=true from rfl,
    ite_true,authority]
  rfl
#print axioms valid

theorem source : NCV_Reference.policy window=
    ok (.Ok (NCV_Carrier.fromPolicy JHg_AccountValues.master.verifier_policy)) := by
  have len : JHg_DataMaster.value.val.length=384 := JHg_DataMaster.length
  have wl : window.val.length=104 := JHg_FieldRead.length _ _ _ (by omega)
  have size : Slice.len window=104#usize := UScalar.eq_of_val_eq wl
  have start:=NCV_FieldViews.read_prefix window 4#usize (by scalar_tac)
  have magic : NCV_Reference.equal (JHg_FieldRead.segment window 0 4)
      (Array.make 4#usize [65#u8,83#u8,80#u8,80#u8]).to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · rw [show window=JHg_FieldRead.segment JHg_DataMaster.value 208 104 from rfl,
        NCV_FieldViews.nested _ 208 104 0 4 (by omega)]
      exact JHg_AuditMaster.policy_magic
  have version : Slice.index_usize window 4#usize=ok 1#u8 :=
    JHu_WindowFields.byte _ 208 104 _ _ (by omega) (by scalar_tac) JHg_AuditMaster.policy_version
  have flags : Slice.index_usize window 5#usize=ok 3#u8 :=
    JHu_WindowFields.byte _ 208 104 _ _ (by omega) (by scalar_tac) JHg_AuditMaster.policy_flags
  have reserved:=JHg_FieldRead.read window 6#usize 8#usize (by scalar_tac) (by scalar_tac)
  have zero : NCV_Reference.zero (JHg_FieldRead.segment window 6 2)=ok true := by
    apply JHu_ZeroFields.zero _ 2 _ (by omega)
    change ((JHg_FieldRead.segment JHg_DataMaster.value 208 104).val.drop 6).take 2=_
    rw [JHu_WindowFields.field _ 208 104 6 2 (by omega)]
    exact JHg_AuditMaster.policy_reserved
  have registry : NCV_Reference.bytes32 window 8#usize=ok JHg_AccountValues.master.verifier_policy.registry_program :=
    JHu_WindowFields.bytes32 _ 208 104 _ _ (by omega) (by omega) (by scalar_tac) JHg_BindingsMaster.registry_program
  have authority : NCV_Reference.bytes32 window 40#usize=ok JHg_AccountValues.master.verifier_policy.registry_authority :=
    JHu_WindowFields.bytes32 _ 208 104 _ _ (by omega) (by omega) (by scalar_tac) JHg_AuditMaster.registry_authority
  have binding : NCV_Reference.bytes32 window 72#usize=ok JHg_AccountValues.master.verifier_policy.policy_binding :=
    JHu_WindowFields.bytes32 _ 208 104 _ _ (by omega) (by omega) (by scalar_tac) JHg_AuditMaster.policy_binding
  have validity : NCV_Reference.valid_policy
      ⟨3#u8,JHg_AccountValues.master.verifier_policy.registry_program,
       JHg_AccountValues.master.verifier_policy.registry_authority,
       JHg_AccountValues.master.verifier_policy.policy_binding⟩=ok true := valid
  simp only [NCV_Reference.policy,size,show (104#usize != 104#usize)=false from rfl,
    Bool.false_eq_true,ite_false,start,lift,bind_tc_ok,
    show (4#usize).val=4 from rfl,show (6#usize).val=6 from rfl,
    show (8#usize).val=8 from rfl,Nat.reduceSub,magic,ite_true,version,
    show (1#u8 != 1#u8)=false from rfl,reserved,zero,flags,registry,authority,binding,validity]
  rfl
#print axioms source
end AspisR1.JHu_MasterPolicy
