import NCV_CastHelpers
import JHg_Scalar00
import JHg_Scalar09
import JHg_Scalar18
set_option autoImplicit false
namespace NCV_FixtureScalars
open Aeneas Aeneas.Std Result AspisR1

theorem master_next : NCV_CastRef.word64 JHg_DataMaster.value 40#usize=ok 43#u64 := by
  have len : JHg_DataMaster.value.val.length=384 := JHg_DataMaster.length
  have field : (JHg_DataMaster.value.val.drop (40#usize).val).take 8=JHg_Scalar00.value.val := JHg_Scalar00.bytes
  have read:=NCV_CastHelpers.word64 _ 40#usize JHg_Scalar00.value (by scalar_tac) field
  rw [JHg_Scalar00.native] at read
  exact read

theorem checkpoint_sequence : NCV_CastRef.word64 JHg_DataForest.value 72#usize=ok 42#u64 := by
  have len : JHg_DataForest.value.val.length=192 := JHg_DataForest.length
  have field : (JHg_DataForest.value.val.drop (72#usize).val).take 8=JHg_Scalar09.value.val := JHg_Scalar09.bytes
  have read:=NCV_CastHelpers.word64 _ 72#usize JHg_Scalar09.value (by scalar_tac) field
  rw [JHg_Scalar09.native] at read
  exact read

theorem lane_next : NCV_CastRef.word64 JHb_DataLane.value 88#usize=ok 13#u64 := by
  have len : JHb_DataLane.value.val.length=768 := JHb_DataLane.length
  have field : (JHb_DataLane.value.val.drop (88#usize).val).take 8=JHg_Scalar18.value.val := JHg_Scalar18.bytes
  have read:=NCV_CastHelpers.word64 _ 88#usize JHg_Scalar18.value (by scalar_tac) field
  rw [JHg_Scalar18.native] at read
  exact read

#print axioms master_next
#print axioms checkpoint_sequence
#print axioms lane_next
end NCV_FixtureScalars
