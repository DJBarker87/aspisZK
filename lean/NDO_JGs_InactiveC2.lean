import NDO_JGs_InactiveData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem coefficient32 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=32#usize,«end»:=64#usize} cs32=ok (.cont ({start:=33#usize,«end»:=64#usize},cs33)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 32#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 32#usize 64#usize 33#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 32#usize=ok (FIo_Install.toE JGo_TX2_Message32.value32) from JGo_TX2_Message32.native_field32]
  with_unfolding_all rfl
#print axioms coefficient32
theorem coefficient33 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=33#usize,«end»:=64#usize} cs33=ok (.cont ({start:=34#usize,«end»:=64#usize},cs34)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 33#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 33#usize 64#usize 34#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 33#usize=ok (FIo_Install.toE JGo_TX2_Message32.value33) from JGo_TX2_Message32.native_field33]
  with_unfolding_all rfl
#print axioms coefficient33
theorem coefficient34 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=34#usize,«end»:=64#usize} cs34=ok (.cont ({start:=35#usize,«end»:=64#usize},cs35)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 34#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 34#usize 64#usize 35#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 34#usize=ok (FIo_Install.toE JGo_TX2_Message32.value34) from JGo_TX2_Message32.native_field34]
  with_unfolding_all rfl
#print axioms coefficient34
theorem coefficient35 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=35#usize,«end»:=64#usize} cs35=ok (.cont ({start:=36#usize,«end»:=64#usize},cs36)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 35#usize=ok 7#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 7#u8=7#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 35#usize 64#usize 36#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 35#usize=ok (FIo_Install.toE JGo_TX2_Message32.value35) from JGo_TX2_Message32.native_field35]
  with_unfolding_all rfl
#print axioms coefficient35
theorem coefficient36 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=36#usize,«end»:=64#usize} cs36=ok (.cont ({start:=37#usize,«end»:=64#usize},cs37)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 36#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 36#usize 64#usize 37#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 36#usize=ok (FIo_Install.toE JGo_TX2_Message32.value36) from JGo_TX2_Message32.native_field36]
  with_unfolding_all rfl
#print axioms coefficient36
theorem coefficient37 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=37#usize,«end»:=64#usize} cs37=ok (.cont ({start:=38#usize,«end»:=64#usize},cs38)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 37#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 37#usize 64#usize 38#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 37#usize=ok (FIo_Install.toE JGo_TX2_Message32.value37) from JGo_TX2_Message32.native_field37]
  with_unfolding_all rfl
#print axioms coefficient37
theorem coefficient38 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=38#usize,«end»:=64#usize} cs38=ok (.cont ({start:=39#usize,«end»:=64#usize},cs39)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 38#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 38#usize 64#usize 39#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 38#usize=ok (FIo_Install.toE JGo_TX2_Message32.value38) from JGo_TX2_Message32.native_field38]
  with_unfolding_all rfl
#print axioms coefficient38
theorem coefficient39 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=39#usize,«end»:=64#usize} cs39=ok (.cont ({start:=40#usize,«end»:=64#usize},cs40)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 39#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 39#usize 64#usize 40#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 39#usize=ok (FIo_Install.toE JGo_TX2_Message32.value39) from JGo_TX2_Message32.native_field39]
  with_unfolding_all rfl
#print axioms coefficient39
theorem coefficient40 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=40#usize,«end»:=64#usize} cs40=ok (.cont ({start:=41#usize,«end»:=64#usize},cs41)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 40#usize=ok 4#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 4#u8=4#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 40#usize 64#usize 41#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 40#usize=ok (FIo_Install.toE JGo_TX2_Message40.value40) from JGo_TX2_Message40.native_field40]
  with_unfolding_all rfl
#print axioms coefficient40
theorem coefficient41 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=41#usize,«end»:=64#usize} cs41=ok (.cont ({start:=42#usize,«end»:=64#usize},cs42)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 41#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 41#usize 64#usize 42#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 41#usize=ok (FIo_Install.toE JGo_TX2_Message40.value41) from JGo_TX2_Message40.native_field41]
  with_unfolding_all rfl
#print axioms coefficient41
theorem coefficient42 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=42#usize,«end»:=64#usize} cs42=ok (.cont ({start:=43#usize,«end»:=64#usize},cs43)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 42#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 42#usize 64#usize 43#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 42#usize=ok (FIo_Install.toE JGo_TX2_Message40.value42) from JGo_TX2_Message40.native_field42]
  with_unfolding_all rfl
#print axioms coefficient42
theorem coefficient43 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=43#usize,«end»:=64#usize} cs43=ok (.cont ({start:=44#usize,«end»:=64#usize},cs44)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 43#usize=ok 5#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 5#u8=5#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 43#usize 64#usize 44#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 43#usize=ok (FIo_Install.toE JGo_TX2_Message40.value43) from JGo_TX2_Message40.native_field43]
  with_unfolding_all rfl
#print axioms coefficient43
theorem coefficient44 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=44#usize,«end»:=64#usize} cs44=ok (.cont ({start:=45#usize,«end»:=64#usize},cs45)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 44#usize=ok 8#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 8#u8=8#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 44#usize 64#usize 45#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 44#usize=ok (FIo_Install.toE JGo_TX2_Message40.value44) from JGo_TX2_Message40.native_field44]
  with_unfolding_all rfl
#print axioms coefficient44
theorem coefficient45 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=45#usize,«end»:=64#usize} cs45=ok (.cont ({start:=46#usize,«end»:=64#usize},cs46)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 45#usize=ok 9#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 9#u8=9#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 45#usize 64#usize 46#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 45#usize=ok (FIo_Install.toE JGo_TX2_Message40.value45) from JGo_TX2_Message40.native_field45]
  with_unfolding_all rfl
#print axioms coefficient45
theorem coefficient46 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=46#usize,«end»:=64#usize} cs46=ok (.cont ({start:=47#usize,«end»:=64#usize},cs47)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 46#usize=ok 10#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 10#u8=10#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 46#usize 64#usize 47#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 46#usize=ok (FIo_Install.toE JGo_TX2_Message40.value46) from JGo_TX2_Message40.native_field46]
  with_unfolding_all rfl
#print axioms coefficient46
theorem coefficient47 : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f
    {start:=47#usize,«end»:=64#usize} cs47=ok (.cont ({start:=48#usize,«end»:=64#usize},cs48)) := by
  have groupRead : Array.index_usize FIo_Native.weights.S2_INACTIVE_GROUPS 47#usize=ok 8#u8 := by with_unfolding_all rfl
  have cast : UScalar.cast .Usize 8#u8=8#usize := UScalar.eq_of_val_eq (by rw [U8.cast_Usize_val_eq];rfl)
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
  rw [JGo_TX2_Range.next 47#usize 64#usize 48#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,groupRead,lift,bind_tc_ok,cast]
  rw [show FIo_Native.weights.field JGq_PairShape.f 47#usize=ok (FIo_Install.toE JGo_TX2_Message40.value47) from JGo_TX2_Message40.native_field47]
  with_unfolding_all rfl
#print axioms coefficient47
end AspisR1.JGs_Inactive
end
