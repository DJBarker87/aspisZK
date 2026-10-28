import NDO_JGs_InactiveData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem coefficient16 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=16#usize,«end»:=64#usize} cs16=ok (.cont ({start:=17#usize,«end»:=64#usize},cs17)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 16#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 16#usize 64#usize 17#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 16#usize=ok (FIo_Install.toE JGo_TX2_Message16.value16) from JGo_TX2_Message16.native_field16]
  with_unfolding_all rfl
#print axioms coefficient16
theorem coefficient17 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=17#usize,«end»:=64#usize} cs17=ok (.cont ({start:=18#usize,«end»:=64#usize},cs18)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 17#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 17#usize 64#usize 18#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 17#usize=ok (FIo_Install.toE JGo_TX2_Message16.value17) from JGo_TX2_Message16.native_field17]
  with_unfolding_all rfl
#print axioms coefficient17
theorem coefficient18 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=18#usize,«end»:=64#usize} cs18=ok (.cont ({start:=19#usize,«end»:=64#usize},cs19)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 18#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 18#usize 64#usize 19#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 18#usize=ok (FIo_Install.toE JGo_TX2_Message16.value18) from JGo_TX2_Message16.native_field18]
  with_unfolding_all rfl
#print axioms coefficient18
theorem coefficient19 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=19#usize,«end»:=64#usize} cs19=ok (.cont ({start:=20#usize,«end»:=64#usize},cs20)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 19#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 19#usize 64#usize 20#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 19#usize=ok (FIo_Install.toE JGo_TX2_Message16.value19) from JGo_TX2_Message16.native_field19]
  with_unfolding_all rfl
#print axioms coefficient19
theorem coefficient20 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=20#usize,«end»:=64#usize} cs20=ok (.cont ({start:=21#usize,«end»:=64#usize},cs21)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 20#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 20#usize 64#usize 21#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 20#usize=ok (FIo_Install.toE JGo_TX2_Message16.value20) from JGo_TX2_Message16.native_field20]
  with_unfolding_all rfl
#print axioms coefficient20
theorem coefficient21 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=21#usize,«end»:=64#usize} cs21=ok (.cont ({start:=22#usize,«end»:=64#usize},cs22)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 21#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 21#usize 64#usize 22#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 21#usize=ok (FIo_Install.toE JGo_TX2_Message16.value21) from JGo_TX2_Message16.native_field21]
  with_unfolding_all rfl
#print axioms coefficient21
theorem coefficient22 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=22#usize,«end»:=64#usize} cs22=ok (.cont ({start:=23#usize,«end»:=64#usize},cs23)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 22#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 22#usize 64#usize 23#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 22#usize=ok (FIo_Install.toE JGo_TX2_Message16.value22) from JGo_TX2_Message16.native_field22]
  with_unfolding_all rfl
#print axioms coefficient22
theorem coefficient23 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=23#usize,«end»:=64#usize} cs23=ok (.cont ({start:=24#usize,«end»:=64#usize},cs24)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 23#usize=ok 6#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 6#u8=6#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 23#usize 64#usize 24#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 23#usize=ok (FIo_Install.toE JGo_TX2_Message16.value23) from JGo_TX2_Message16.native_field23]
  with_unfolding_all rfl
#print axioms coefficient23
theorem coefficient24 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=24#usize,«end»:=64#usize} cs24=ok (.cont ({start:=25#usize,«end»:=64#usize},cs25)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 24#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 24#usize 64#usize 25#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 24#usize=ok (FIo_Install.toE JGo_TX2_Message24.value24) from JGo_TX2_Message24.native_field24]
  with_unfolding_all rfl
#print axioms coefficient24
theorem coefficient25 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=25#usize,«end»:=64#usize} cs25=ok (.cont ({start:=26#usize,«end»:=64#usize},cs26)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 25#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 25#usize 64#usize 26#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 25#usize=ok (FIo_Install.toE JGo_TX2_Message24.value25) from JGo_TX2_Message24.native_field25]
  with_unfolding_all rfl
#print axioms coefficient25
theorem coefficient26 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=26#usize,«end»:=64#usize} cs26=ok (.cont ({start:=27#usize,«end»:=64#usize},cs27)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 26#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 26#usize 64#usize 27#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 26#usize=ok (FIo_Install.toE JGo_TX2_Message24.value26) from JGo_TX2_Message24.native_field26]
  with_unfolding_all rfl
#print axioms coefficient26
theorem coefficient27 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=27#usize,«end»:=64#usize} cs27=ok (.cont ({start:=28#usize,«end»:=64#usize},cs28)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 27#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 27#usize 64#usize 28#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 27#usize=ok (FIo_Install.toE JGo_TX2_Message24.value27) from JGo_TX2_Message24.native_field27]
  with_unfolding_all rfl
#print axioms coefficient27
theorem coefficient28 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=28#usize,«end»:=64#usize} cs28=ok (.cont ({start:=29#usize,«end»:=64#usize},cs29)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 28#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 28#usize 64#usize 29#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 28#usize=ok (FIo_Install.toE JGo_TX2_Message24.value28) from JGo_TX2_Message24.native_field28]
  with_unfolding_all rfl
#print axioms coefficient28
theorem coefficient29 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=29#usize,«end»:=64#usize} cs29=ok (.cont ({start:=30#usize,«end»:=64#usize},cs30)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 29#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 29#usize 64#usize 30#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 29#usize=ok (FIo_Install.toE JGo_TX2_Message24.value29) from JGo_TX2_Message24.native_field29]
  with_unfolding_all rfl
#print axioms coefficient29
theorem coefficient30 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=30#usize,«end»:=64#usize} cs30=ok (.cont ({start:=31#usize,«end»:=64#usize},cs31)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 30#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 30#usize 64#usize 31#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 30#usize=ok (FIo_Install.toE JGo_TX2_Message24.value30) from JGo_TX2_Message24.native_field30]
  with_unfolding_all rfl
#print axioms coefficient30
theorem coefficient31 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=31#usize,«end»:=64#usize} cs31=ok (.cont ({start:=32#usize,«end»:=64#usize},cs32)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 31#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 31#usize 64#usize 32#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 31#usize=ok (FIo_Install.toE JGo_TX2_Message24.value31) from JGo_TX2_Message24.native_field31]
  with_unfolding_all rfl
#print axioms coefficient31
end AspisR1.JGs_Inactive
end
