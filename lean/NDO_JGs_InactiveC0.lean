import NDO_JGs_InactiveData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem coefficient0 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=0#usize,«end»:=64#usize} cs0=ok (.cont ({start:=1#usize,«end»:=64#usize},cs1)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 0#usize=ok 0#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 0#u8=0#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 0#usize 64#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 0#usize=ok (FIo_Install.toE JGo_TX2_Message00.value00) from JGo_TX2_Message00.native_field00]
  with_unfolding_all rfl
#print axioms coefficient0
theorem coefficient1 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=1#usize,«end»:=64#usize} cs1=ok (.cont ({start:=2#usize,«end»:=64#usize},cs2)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 1#usize=ok 1#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 1#u8=1#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 1#usize 64#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 1#usize=ok (FIo_Install.toE JGo_TX2_Message00.value01) from JGo_TX2_Message00.native_field01]
  with_unfolding_all rfl
#print axioms coefficient1
theorem coefficient2 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=2#usize,«end»:=64#usize} cs2=ok (.cont ({start:=3#usize,«end»:=64#usize},cs3)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 2#usize=ok 2#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 2#u8=2#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 2#usize 64#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 2#usize=ok (FIo_Install.toE JGo_TX2_Message00.value02) from JGo_TX2_Message00.native_field02]
  with_unfolding_all rfl
#print axioms coefficient2
theorem coefficient3 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=3#usize,«end»:=64#usize} cs3=ok (.cont ({start:=4#usize,«end»:=64#usize},cs4)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 3#usize=ok 3#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 3#u8=3#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 3#usize 64#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 3#usize=ok (FIo_Install.toE JGo_TX2_Message00.value03) from JGo_TX2_Message00.native_field03]
  with_unfolding_all rfl
#print axioms coefficient3
theorem coefficient4 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=4#usize,«end»:=64#usize} cs4=ok (.cont ({start:=5#usize,«end»:=64#usize},cs5)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 4#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 4#usize 64#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 4#usize=ok (FIo_Install.toE JGo_TX2_Message00.value04) from JGo_TX2_Message00.native_field04]
  with_unfolding_all rfl
#print axioms coefficient4
theorem coefficient5 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=5#usize,«end»:=64#usize} cs5=ok (.cont ({start:=6#usize,«end»:=64#usize},cs6)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 5#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 5#usize 64#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 5#usize=ok (FIo_Install.toE JGo_TX2_Message00.value05) from JGo_TX2_Message00.native_field05]
  with_unfolding_all rfl
#print axioms coefficient5
theorem coefficient6 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=6#usize,«end»:=64#usize} cs6=ok (.cont ({start:=7#usize,«end»:=64#usize},cs7)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 6#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 6#usize 64#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 6#usize=ok (FIo_Install.toE JGo_TX2_Message00.value06) from JGo_TX2_Message00.native_field06]
  with_unfolding_all rfl
#print axioms coefficient6
theorem coefficient7 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=7#usize,«end»:=64#usize} cs7=ok (.cont ({start:=8#usize,«end»:=64#usize},cs8)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 7#usize=ok 6#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 6#u8=6#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 7#usize 64#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 7#usize=ok (FIo_Install.toE JGo_TX2_Message00.value07) from JGo_TX2_Message00.native_field07]
  with_unfolding_all rfl
#print axioms coefficient7
theorem coefficient8 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=8#usize,«end»:=64#usize} cs8=ok (.cont ({start:=9#usize,«end»:=64#usize},cs9)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 8#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 8#usize 64#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 8#usize=ok (FIo_Install.toE JGo_TX2_Message08.value08) from JGo_TX2_Message08.native_field08]
  with_unfolding_all rfl
#print axioms coefficient8
theorem coefficient9 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=9#usize,«end»:=64#usize} cs9=ok (.cont ({start:=10#usize,«end»:=64#usize},cs10)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 9#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 9#usize 64#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 9#usize=ok (FIo_Install.toE JGo_TX2_Message08.value09) from JGo_TX2_Message08.native_field09]
  with_unfolding_all rfl
#print axioms coefficient9
theorem coefficient10 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=10#usize,«end»:=64#usize} cs10=ok (.cont ({start:=11#usize,«end»:=64#usize},cs11)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 10#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 10#usize 64#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 10#usize=ok (FIo_Install.toE JGo_TX2_Message08.value10) from JGo_TX2_Message08.native_field10]
  with_unfolding_all rfl
#print axioms coefficient10
theorem coefficient11 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=11#usize,«end»:=64#usize} cs11=ok (.cont ({start:=12#usize,«end»:=64#usize},cs12)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 11#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 11#usize 64#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 11#usize=ok (FIo_Install.toE JGo_TX2_Message08.value11) from JGo_TX2_Message08.native_field11]
  with_unfolding_all rfl
#print axioms coefficient11
theorem coefficient12 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=12#usize,«end»:=64#usize} cs12=ok (.cont ({start:=13#usize,«end»:=64#usize},cs13)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 12#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 12#usize 64#usize 13#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 12#usize=ok (FIo_Install.toE JGo_TX2_Message08.value12) from JGo_TX2_Message08.native_field12]
  with_unfolding_all rfl
#print axioms coefficient12
theorem coefficient13 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=13#usize,«end»:=64#usize} cs13=ok (.cont ({start:=14#usize,«end»:=64#usize},cs14)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 13#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 13#usize 64#usize 14#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 13#usize=ok (FIo_Install.toE JGo_TX2_Message08.value13) from JGo_TX2_Message08.native_field13]
  with_unfolding_all rfl
#print axioms coefficient13
theorem coefficient14 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=14#usize,«end»:=64#usize} cs14=ok (.cont ({start:=15#usize,«end»:=64#usize},cs15)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 14#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 14#usize 64#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 14#usize=ok (FIo_Install.toE JGo_TX2_Message08.value14) from JGo_TX2_Message08.native_field14]
  with_unfolding_all rfl
#print axioms coefficient14
theorem coefficient15 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=15#usize,«end»:=64#usize} cs15=ok (.cont ({start:=16#usize,«end»:=64#usize},cs16)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 15#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 15#usize 64#usize 16#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 15#usize=ok (FIo_Install.toE JGo_TX2_Message08.value15) from JGo_TX2_Message08.native_field15]
  with_unfolding_all rfl
#print axioms coefficient15
end AspisR1.JGs_Inactive
end
