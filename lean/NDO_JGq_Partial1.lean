import NDO_JGq_PartialPush1_0
import NDO_JGq_PartialPush1_1
import NDO_JGq_PartialPush1_2
import NDO_JGq_PartialPush1_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish d1_16=ok value1 := by with_unfolding_all rfl
#print axioms finish1
theorem step1_0 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=0#usize,«end»:=16#usize} d1_0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},d1_1)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 0#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 0#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 0#usize=ok JGq_Common.c0 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 16#usize=ok (FIo_Install.toE JGo_TX2_Message16.value16) from JGo_TX2_Message16.native_field16,bind_tc_ok,
    read,bind_tc_ok,push1_0,bind_tc_ok]
  rfl
#print axioms step1_0
theorem step1_1 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=1#usize,«end»:=16#usize} d1_1=
    ok (.cont ({start:=2#usize,«end»:=16#usize},d1_2)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 1#usize=17#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 1#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 1#usize=ok JGq_Common.c1 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 17#usize=ok (FIo_Install.toE JGo_TX2_Message16.value17) from JGo_TX2_Message16.native_field17,bind_tc_ok,
    read,bind_tc_ok,push1_1,bind_tc_ok]
  rfl
#print axioms step1_1
theorem step1_2 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=2#usize,«end»:=16#usize} d1_2=
    ok (.cont ({start:=3#usize,«end»:=16#usize},d1_3)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 2#usize=18#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 2#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 2#usize=ok JGq_Common.c2 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 18#usize=ok (FIo_Install.toE JGo_TX2_Message16.value18) from JGo_TX2_Message16.native_field18,bind_tc_ok,
    read,bind_tc_ok,push1_2,bind_tc_ok]
  rfl
#print axioms step1_2
theorem step1_3 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=3#usize,«end»:=16#usize} d1_3=
    ok (.cont ({start:=4#usize,«end»:=16#usize},d1_4)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 3#usize=19#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 3#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 3#usize=ok JGq_Common.c3 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 19#usize=ok (FIo_Install.toE JGo_TX2_Message16.value19) from JGo_TX2_Message16.native_field19,bind_tc_ok,
    read,bind_tc_ok,push1_3,bind_tc_ok]
  rfl
#print axioms step1_3
theorem step1_4 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=4#usize,«end»:=16#usize} d1_4=
    ok (.cont ({start:=5#usize,«end»:=16#usize},d1_5)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 4#usize=20#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 4#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 4#usize=ok JGq_Common.c4 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 4#usize 16#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 20#usize=ok (FIo_Install.toE JGo_TX2_Message16.value20) from JGo_TX2_Message16.native_field20,bind_tc_ok,
    read,bind_tc_ok,push1_4,bind_tc_ok]
  rfl
#print axioms step1_4
theorem step1_5 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=5#usize,«end»:=16#usize} d1_5=
    ok (.cont ({start:=6#usize,«end»:=16#usize},d1_6)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 5#usize=21#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 5#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 5#usize=ok JGq_Common.c5 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 5#usize 16#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 21#usize=ok (FIo_Install.toE JGo_TX2_Message16.value21) from JGo_TX2_Message16.native_field21,bind_tc_ok,
    read,bind_tc_ok,push1_5,bind_tc_ok]
  rfl
#print axioms step1_5
theorem step1_6 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=6#usize,«end»:=16#usize} d1_6=
    ok (.cont ({start:=7#usize,«end»:=16#usize},d1_7)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 6#usize=22#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 6#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 6#usize=ok JGq_Common.c6 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 6#usize 16#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 22#usize=ok (FIo_Install.toE JGo_TX2_Message16.value22) from JGo_TX2_Message16.native_field22,bind_tc_ok,
    read,bind_tc_ok,push1_6,bind_tc_ok]
  rfl
#print axioms step1_6
theorem step1_7 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=7#usize,«end»:=16#usize} d1_7=
    ok (.cont ({start:=8#usize,«end»:=16#usize},d1_8)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 7#usize=23#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 7#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 7#usize=ok JGq_Common.c7 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 7#usize 16#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 23#usize=ok (FIo_Install.toE JGo_TX2_Message16.value23) from JGo_TX2_Message16.native_field23,bind_tc_ok,
    read,bind_tc_ok,push1_7,bind_tc_ok]
  rfl
#print axioms step1_7
theorem step1_8 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=8#usize,«end»:=16#usize} d1_8=
    ok (.cont ({start:=9#usize,«end»:=16#usize},d1_9)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 8#usize=24#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 8#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 8#usize=ok JGq_Common.c8 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 8#usize 16#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 24#usize=ok (FIo_Install.toE JGo_TX2_Message24.value24) from JGo_TX2_Message24.native_field24,bind_tc_ok,
    read,bind_tc_ok,push1_8,bind_tc_ok]
  rfl
#print axioms step1_8
theorem step1_9 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=9#usize,«end»:=16#usize} d1_9=
    ok (.cont ({start:=10#usize,«end»:=16#usize},d1_10)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 9#usize=25#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 9#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 9#usize=ok JGq_Common.c9 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 9#usize 16#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 25#usize=ok (FIo_Install.toE JGo_TX2_Message24.value25) from JGo_TX2_Message24.native_field25,bind_tc_ok,
    read,bind_tc_ok,push1_9,bind_tc_ok]
  rfl
#print axioms step1_9
theorem step1_10 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=10#usize,«end»:=16#usize} d1_10=
    ok (.cont ({start:=11#usize,«end»:=16#usize},d1_11)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 10#usize=26#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 10#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 10#usize=ok JGq_Common.c10 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 10#usize 16#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 26#usize=ok (FIo_Install.toE JGo_TX2_Message24.value26) from JGo_TX2_Message24.native_field26,bind_tc_ok,
    read,bind_tc_ok,push1_10,bind_tc_ok]
  rfl
#print axioms step1_10
theorem step1_11 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=11#usize,«end»:=16#usize} d1_11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},d1_12)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 11#usize=27#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 11#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 11#usize=ok JGq_Common.c11 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 27#usize=ok (FIo_Install.toE JGo_TX2_Message24.value27) from JGo_TX2_Message24.native_field27,bind_tc_ok,
    read,bind_tc_ok,push1_11,bind_tc_ok]
  rfl
#print axioms step1_11
theorem step1_12 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=12#usize,«end»:=16#usize} d1_12=
    ok (.cont ({start:=13#usize,«end»:=16#usize},d1_13)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 12#usize=28#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 12#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 12#usize=ok JGq_Common.c12 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 12#usize 16#usize 13#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 28#usize=ok (FIo_Install.toE JGo_TX2_Message24.value28) from JGo_TX2_Message24.native_field28,bind_tc_ok,
    read,bind_tc_ok,push1_12,bind_tc_ok]
  rfl
#print axioms step1_12
theorem step1_13 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=13#usize,«end»:=16#usize} d1_13=
    ok (.cont ({start:=14#usize,«end»:=16#usize},d1_14)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 13#usize=29#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 13#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 13#usize=ok JGq_Common.c13 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 13#usize 16#usize 14#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 29#usize=ok (FIo_Install.toE JGo_TX2_Message24.value29) from JGo_TX2_Message24.native_field29,bind_tc_ok,
    read,bind_tc_ok,push1_13,bind_tc_ok]
  rfl
#print axioms step1_13
theorem step1_14 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=14#usize,«end»:=16#usize} d1_14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},d1_15)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 14#usize=30#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 14#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 14#usize=ok JGq_Common.c14 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 30#usize=ok (FIo_Install.toE JGo_TX2_Message24.value30) from JGo_TX2_Message24.native_field30,bind_tc_ok,
    read,bind_tc_ok,push1_14,bind_tc_ok]
  rfl
#print axioms step1_14
theorem step1_15 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
    {start:=15#usize,«end»:=16#usize} d1_15=
    ok (.cont ({start:=16#usize,«end»:=16#usize},d1_16)) := by
  have mul : Usize.wrapping_mul 16#usize 1#usize=16#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 1#usize (by decide))
  have add : Usize.wrapping_add 16#usize 15#usize=31#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 16#usize 15#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 15#usize=ok JGq_Common.c15 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 15#usize 16#usize 16#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 31#usize=ok (FIo_Install.toE JGo_TX2_Message24.value31) from JGo_TX2_Message24.native_field31,bind_tc_ok,
    read,bind_tc_ok,push1_15,bind_tc_ok]
  rfl
#print axioms step1_15
abbrev S1 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states1 : Nat → S1
  | 0 => ({start:=0#usize,«end»:=16#usize},d1_0)
  | 1 => ({start:=1#usize,«end»:=16#usize},d1_1)
  | 2 => ({start:=2#usize,«end»:=16#usize},d1_2)
  | 3 => ({start:=3#usize,«end»:=16#usize},d1_3)
  | 4 => ({start:=4#usize,«end»:=16#usize},d1_4)
  | 5 => ({start:=5#usize,«end»:=16#usize},d1_5)
  | 6 => ({start:=6#usize,«end»:=16#usize},d1_6)
  | 7 => ({start:=7#usize,«end»:=16#usize},d1_7)
  | 8 => ({start:=8#usize,«end»:=16#usize},d1_8)
  | 9 => ({start:=9#usize,«end»:=16#usize},d1_9)
  | 10 => ({start:=10#usize,«end»:=16#usize},d1_10)
  | 11 => ({start:=11#usize,«end»:=16#usize},d1_11)
  | 12 => ({start:=12#usize,«end»:=16#usize},d1_12)
  | 13 => ({start:=13#usize,«end»:=16#usize},d1_13)
  | 14 => ({start:=14#usize,«end»:=16#usize},d1_14)
  | 15 => ({start:=15#usize,«end»:=16#usize},d1_15)
  | _ => ({start:=16#usize,«end»:=16#usize},d1_16)
theorem source1 : FIo_Native.weights.partial_dot f JGq_Common.a16 1#usize=ok (.Ok value1) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d1_0 := by rfl
  unfold FIo_Native.weights.partial_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.partial_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S1=>FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize x.1 x.2)
    states1 16 (.Ok value1)
  · intro i hi
    interval_cases i
    · exact step1_0
    · exact step1_1
    · exact step1_2
    · exact step1_3
    · exact step1_4
    · exact step1_5
    · exact step1_6
    · exact step1_7
    · exact step1_8
    · exact step1_9
    · exact step1_10
    · exact step1_11
    · exact step1_12
    · exact step1_13
    · exact step1_14
    · exact step1_15
  · change FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 1#usize
        {start:=16#usize,«end»:=16#usize} d1_16=ok (.done (.Ok value1))
    unfold FIo_Native.weights.partial_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=16#usize,«end»:=16#usize} : core.ops.range.Range Usize)=ok (none,{start:=16#usize,«end»:=16#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish1,bind_tc_ok]
#print axioms source1
end AspisR1.JGq_Partial
end
