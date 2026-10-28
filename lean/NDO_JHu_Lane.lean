import NDO_JHu_FrontierFixture
import NDO_JHu_WindowFields
import NCV_Install
set_option autoImplicit false
namespace AspisR1.JHu_Lane
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.bytes

theorem source : NCV_Reference.decode_lane_ref JHb_DataLane.value=
    ok (.Ok (NCV_Carrier.fromLane JHg_AccountValues.lane)) := by
  have len : JHb_DataLane.value.val.length=768 := JHb_DataLane.length
  have size : Slice.len JHb_DataLane.value=768#usize := UScalar.eq_of_val_eq len
  have start:=NCV_FieldViews.read_prefix JHb_DataLane.value 4#usize (by scalar_tac)
  have magic : NCV_Reference.equal (JHg_FieldRead.segment JHb_DataLane.value 0 4)
      (Array.make 4#usize [65#u8,83#u8,76#u8,56#u8]).to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · exact JHg_AuditLane.magic
  have version : Slice.index_usize JHb_DataLane.value 4#usize=ok 2#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditLane.version
  have lane : Slice.index_usize JHb_DataLane.value 5#usize=ok 3#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditLane.lane
  have lanes : Slice.index_usize JHb_DataLane.value 6#usize=ok 8#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditLane.lanes
  have depth : Slice.index_usize JHb_DataLane.value 7#usize=ok 20#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditLane.depth
  have bindingRead:=JHg_FieldRead.read JHb_DataLane.value 8#usize 40#usize (by scalar_tac) (by scalar_tac)
  have binding : NCV_Reference.equal (JHg_FieldRead.segment JHb_DataLane.value 8 32)
      NCV_Reference.BINDING.to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 8 32 (by omega)];omega
    · unfold NCV_Reference.BINDING
      exact JHg_AuditLane.format
  have reserved:=JHg_FieldRead.read JHb_DataLane.value 73#usize 80#usize (by scalar_tac) (by scalar_tac)
  have zero : NCV_Reference.zero (JHg_FieldRead.segment JHb_DataLane.value 73 7)=ok true :=
    JHu_ZeroFields.zero _ 7 JHg_AuditLane.reserved (by omega)
  have master : NCV_Reference.bytes32 JHb_DataLane.value 40#usize=ok JHg_AccountValues.lane.master :=
    JHu_ReferenceBytes.bytes32 _ _ _ (by omega) (by scalar_tac) JHg_AuditLane.master
  have nonzero : NCV_Reference.zero JHg_AccountValues.lane.master.to_slice=ok false := by
    apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768;omega
    · change (34#u8 : U8) ≠ 0#u8;scalar_tac
    · change 0<32;omega
  have treeRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      JHb_DataLane.value {start:=80#usize}=ok JHu_FixtureDigests.tree := by
    have h:=MultiproofConeSlices.drop_total JHb_DataLane.value 80#usize (by scalar_tac)
    rw [NCV_FieldViews.suffix,len] at h
    exact h
  have tl : JHu_FixtureDigests.tree.val.length=688 := JHu_FixtureDigests.tree_length
  have treeStart:=NCV_FieldViews.read_prefix JHu_FixtureDigests.tree 4#usize (by scalar_tac)
  have treeMagic : NCV_Reference.equal (JHg_FieldRead.segment JHu_FixtureDigests.tree 0 4)
      (Array.make 4#usize [65#u8,83#u8,80#u8,84#u8]).to_slice=ok true := by
    apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · rw [show JHu_FixtureDigests.tree=JHg_FieldRead.segment JHb_DataLane.value 80 688 from rfl,
        NCV_FieldViews.nested _ 80 688 0 4 (by omega)]
      exact JHg_AuditLane.tree_magic
  have treeVersion : Slice.index_usize JHu_FixtureDigests.tree 4#usize=ok 1#u8 :=
    JHu_WindowFields.byte _ 80 688 _ _ (by omega) (by scalar_tac) JHg_AuditLane.tree_version
  have treeDepth : Slice.index_usize JHu_FixtureDigests.tree 5#usize=ok 20#u8 :=
    JHu_WindowFields.byte _ 80 688 _ _ (by omega) (by scalar_tac) JHg_AuditLane.tree_depth
  have treeHash : Slice.index_usize JHu_FixtureDigests.tree 6#usize=ok 3#u8 :=
    JHu_WindowFields.byte _ 80 688 _ _ (by omega) (by scalar_tac) JHg_AuditLane.tree_hash_version
  have treeEncoding : Slice.index_usize JHu_FixtureDigests.tree 7#usize=ok 1#u8 :=
    JHu_WindowFields.byte _ 80 688 _ _ (by omega) (by scalar_tac) JHg_AuditLane.tree_encoding
  have next : NCV_Reference.word64 JHu_FixtureDigests.tree 8#usize=ok 13#u64 := by
    have field : (JHu_FixtureDigests.tree.val.drop 8).take 8=JHg_Scalar18.value.val := by
      rw [show JHu_FixtureDigests.tree=JHg_FieldRead.segment JHb_DataLane.value 80 688 from rfl,
        JHu_WindowFields.field _ 80 688 8 8 (by omega)]
      exact JHg_Scalar18.bytes
    exact JHu_ReferenceWords.word64 _ _ JHg_Scalar18.value (by omega) (by scalar_tac) field
  have bump : Slice.index_usize JHb_DataLane.value 72#usize=ok 255#u8 :=
    NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditLane.bump
  have laneBound : ¬(3#u8 : U8) >=8#u8 := by scalar_tac
  have nextBound : ¬(13#u64 : U64)>1048576#u64 := by scalar_tac
  have nextNonzero : ¬(13#u64 : U64)=0#u64 := by scalar_tac
  simp only [NCV_Reference.decode_lane_ref,size,show (768#usize != 768#usize)=false from rfl,
    Bool.false_eq_true,ite_false,start,lift,bind_tc_ok,
    show (4#usize).val=4 from rfl,show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,show (73#usize).val=73 from rfl,
    show (80#usize).val=80 from rfl,Nat.reduceSub,
    magic,ite_true,version,show (2#u8 != 2#u8)=false from rfl,
    lane,laneBound,lanes,show (8#u8 != 8#u8)=false from rfl,
    depth,show (20#u8 != 20#u8)=false from rfl,bindingRead,binding,reserved,zero,
    master,nonzero,treeRead,treeStart,treeMagic,treeVersion,
    show (1#u8 != 1#u8)=false from rfl,treeDepth,treeHash,
    show (3#u8 != 3#u8)=false from rfl,treeEncoding,next,nextBound,
    JHu_FixtureDigests.lane_root,JHu_FrontierFixture.source,
    core.result.Result.Insts.CoreOpsTry.branch,nextNonzero,bump]
  rfl
#print axioms source

theorem observation : NCV_Install.op50 JHb_DataLane.value=ok (.Ok JHg_AccountValues.lane) := by
  simp only [NCV_Install.op50,source,bind_tc_ok,NCV_Install.mapReturn,NCV_Carrier.lane_surjective]
#print axioms observation
end AspisR1.JHu_Lane
