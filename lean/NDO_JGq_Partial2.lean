import NDO_JGq_PartialPush2_0
import NDO_JGq_PartialPush2_1
import NDO_JGq_PartialPush2_2
import NDO_JGq_PartialPush2_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish d2_16=ok value2 := by with_unfolding_all rfl
#print axioms finish2
theorem step2_0 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=0#usize,«end»:=16#usize} d2_0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},d2_1)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 0#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 0#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 0#usize=ok JGq_Common.c0 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 32#usize=ok (FIo_Install.toE JGo_TX2_Message32.value32) from JGo_TX2_Message32.native_field32,bind_tc_ok,
    read,bind_tc_ok,push2_0,bind_tc_ok]
  rfl
#print axioms step2_0
theorem step2_1 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=1#usize,«end»:=16#usize} d2_1=
    ok (.cont ({start:=2#usize,«end»:=16#usize},d2_2)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 1#usize=33#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 1#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 1#usize=ok JGq_Common.c1 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 33#usize=ok (FIo_Install.toE JGo_TX2_Message32.value33) from JGo_TX2_Message32.native_field33,bind_tc_ok,
    read,bind_tc_ok,push2_1,bind_tc_ok]
  rfl
#print axioms step2_1
theorem step2_2 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=2#usize,«end»:=16#usize} d2_2=
    ok (.cont ({start:=3#usize,«end»:=16#usize},d2_3)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 2#usize=34#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 2#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 2#usize=ok JGq_Common.c2 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 34#usize=ok (FIo_Install.toE JGo_TX2_Message32.value34) from JGo_TX2_Message32.native_field34,bind_tc_ok,
    read,bind_tc_ok,push2_2,bind_tc_ok]
  rfl
#print axioms step2_2
theorem step2_3 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=3#usize,«end»:=16#usize} d2_3=
    ok (.cont ({start:=4#usize,«end»:=16#usize},d2_4)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 3#usize=35#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 3#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 3#usize=ok JGq_Common.c3 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 35#usize=ok (FIo_Install.toE JGo_TX2_Message32.value35) from JGo_TX2_Message32.native_field35,bind_tc_ok,
    read,bind_tc_ok,push2_3,bind_tc_ok]
  rfl
#print axioms step2_3
theorem step2_4 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=4#usize,«end»:=16#usize} d2_4=
    ok (.cont ({start:=5#usize,«end»:=16#usize},d2_5)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 4#usize=36#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 4#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 4#usize=ok JGq_Common.c4 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 4#usize 16#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 36#usize=ok (FIo_Install.toE JGo_TX2_Message32.value36) from JGo_TX2_Message32.native_field36,bind_tc_ok,
    read,bind_tc_ok,push2_4,bind_tc_ok]
  rfl
#print axioms step2_4
theorem step2_5 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=5#usize,«end»:=16#usize} d2_5=
    ok (.cont ({start:=6#usize,«end»:=16#usize},d2_6)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 5#usize=37#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 5#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 5#usize=ok JGq_Common.c5 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 5#usize 16#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 37#usize=ok (FIo_Install.toE JGo_TX2_Message32.value37) from JGo_TX2_Message32.native_field37,bind_tc_ok,
    read,bind_tc_ok,push2_5,bind_tc_ok]
  rfl
#print axioms step2_5
theorem step2_6 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=6#usize,«end»:=16#usize} d2_6=
    ok (.cont ({start:=7#usize,«end»:=16#usize},d2_7)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 6#usize=38#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 6#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 6#usize=ok JGq_Common.c6 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 6#usize 16#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 38#usize=ok (FIo_Install.toE JGo_TX2_Message32.value38) from JGo_TX2_Message32.native_field38,bind_tc_ok,
    read,bind_tc_ok,push2_6,bind_tc_ok]
  rfl
#print axioms step2_6
theorem step2_7 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=7#usize,«end»:=16#usize} d2_7=
    ok (.cont ({start:=8#usize,«end»:=16#usize},d2_8)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 7#usize=39#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 7#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 7#usize=ok JGq_Common.c7 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 7#usize 16#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 39#usize=ok (FIo_Install.toE JGo_TX2_Message32.value39) from JGo_TX2_Message32.native_field39,bind_tc_ok,
    read,bind_tc_ok,push2_7,bind_tc_ok]
  rfl
#print axioms step2_7
theorem step2_8 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=8#usize,«end»:=16#usize} d2_8=
    ok (.cont ({start:=9#usize,«end»:=16#usize},d2_9)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 8#usize=40#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 8#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 8#usize=ok JGq_Common.c8 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 8#usize 16#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 40#usize=ok (FIo_Install.toE JGo_TX2_Message40.value40) from JGo_TX2_Message40.native_field40,bind_tc_ok,
    read,bind_tc_ok,push2_8,bind_tc_ok]
  rfl
#print axioms step2_8
theorem step2_9 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=9#usize,«end»:=16#usize} d2_9=
    ok (.cont ({start:=10#usize,«end»:=16#usize},d2_10)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 9#usize=41#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 9#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 9#usize=ok JGq_Common.c9 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 9#usize 16#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 41#usize=ok (FIo_Install.toE JGo_TX2_Message40.value41) from JGo_TX2_Message40.native_field41,bind_tc_ok,
    read,bind_tc_ok,push2_9,bind_tc_ok]
  rfl
#print axioms step2_9
theorem step2_10 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=10#usize,«end»:=16#usize} d2_10=
    ok (.cont ({start:=11#usize,«end»:=16#usize},d2_11)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 10#usize=42#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 10#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 10#usize=ok JGq_Common.c10 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 10#usize 16#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 42#usize=ok (FIo_Install.toE JGo_TX2_Message40.value42) from JGo_TX2_Message40.native_field42,bind_tc_ok,
    read,bind_tc_ok,push2_10,bind_tc_ok]
  rfl
#print axioms step2_10
theorem step2_11 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=11#usize,«end»:=16#usize} d2_11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},d2_12)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 11#usize=43#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 11#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 11#usize=ok JGq_Common.c11 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 43#usize=ok (FIo_Install.toE JGo_TX2_Message40.value43) from JGo_TX2_Message40.native_field43,bind_tc_ok,
    read,bind_tc_ok,push2_11,bind_tc_ok]
  rfl
#print axioms step2_11
theorem step2_12 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=12#usize,«end»:=16#usize} d2_12=
    ok (.cont ({start:=13#usize,«end»:=16#usize},d2_13)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 12#usize=44#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 12#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 12#usize=ok JGq_Common.c12 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 12#usize 16#usize 13#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 44#usize=ok (FIo_Install.toE JGo_TX2_Message40.value44) from JGo_TX2_Message40.native_field44,bind_tc_ok,
    read,bind_tc_ok,push2_12,bind_tc_ok]
  rfl
#print axioms step2_12
theorem step2_13 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=13#usize,«end»:=16#usize} d2_13=
    ok (.cont ({start:=14#usize,«end»:=16#usize},d2_14)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 13#usize=45#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 13#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 13#usize=ok JGq_Common.c13 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 13#usize 16#usize 14#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 45#usize=ok (FIo_Install.toE JGo_TX2_Message40.value45) from JGo_TX2_Message40.native_field45,bind_tc_ok,
    read,bind_tc_ok,push2_13,bind_tc_ok]
  rfl
#print axioms step2_13
theorem step2_14 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=14#usize,«end»:=16#usize} d2_14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},d2_15)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 14#usize=46#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 14#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 14#usize=ok JGq_Common.c14 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 46#usize=ok (FIo_Install.toE JGo_TX2_Message40.value46) from JGo_TX2_Message40.native_field46,bind_tc_ok,
    read,bind_tc_ok,push2_14,bind_tc_ok]
  rfl
#print axioms step2_14
theorem step2_15 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
    {start:=15#usize,«end»:=16#usize} d2_15=
    ok (.cont ({start:=16#usize,«end»:=16#usize},d2_16)) := by
  have mul : Usize.wrapping_mul 16#usize 2#usize=32#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 2#usize (by decide))
  have add : Usize.wrapping_add 32#usize 15#usize=47#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 32#usize 15#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 15#usize=ok JGq_Common.c15 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 15#usize 16#usize 16#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 47#usize=ok (FIo_Install.toE JGo_TX2_Message40.value47) from JGo_TX2_Message40.native_field47,bind_tc_ok,
    read,bind_tc_ok,push2_15,bind_tc_ok]
  rfl
#print axioms step2_15
abbrev S2 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states2 : Nat → S2
  | 0 => ({start:=0#usize,«end»:=16#usize},d2_0)
  | 1 => ({start:=1#usize,«end»:=16#usize},d2_1)
  | 2 => ({start:=2#usize,«end»:=16#usize},d2_2)
  | 3 => ({start:=3#usize,«end»:=16#usize},d2_3)
  | 4 => ({start:=4#usize,«end»:=16#usize},d2_4)
  | 5 => ({start:=5#usize,«end»:=16#usize},d2_5)
  | 6 => ({start:=6#usize,«end»:=16#usize},d2_6)
  | 7 => ({start:=7#usize,«end»:=16#usize},d2_7)
  | 8 => ({start:=8#usize,«end»:=16#usize},d2_8)
  | 9 => ({start:=9#usize,«end»:=16#usize},d2_9)
  | 10 => ({start:=10#usize,«end»:=16#usize},d2_10)
  | 11 => ({start:=11#usize,«end»:=16#usize},d2_11)
  | 12 => ({start:=12#usize,«end»:=16#usize},d2_12)
  | 13 => ({start:=13#usize,«end»:=16#usize},d2_13)
  | 14 => ({start:=14#usize,«end»:=16#usize},d2_14)
  | 15 => ({start:=15#usize,«end»:=16#usize},d2_15)
  | _ => ({start:=16#usize,«end»:=16#usize},d2_16)
theorem source2 : FIo_Native.weights.partial_dot f JGq_Common.a16 2#usize=ok (.Ok value2) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d2_0 := by rfl
  unfold FIo_Native.weights.partial_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.partial_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S2=>FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize x.1 x.2)
    states2 16 (.Ok value2)
  · intro i hi
    interval_cases i
    · exact step2_0
    · exact step2_1
    · exact step2_2
    · exact step2_3
    · exact step2_4
    · exact step2_5
    · exact step2_6
    · exact step2_7
    · exact step2_8
    · exact step2_9
    · exact step2_10
    · exact step2_11
    · exact step2_12
    · exact step2_13
    · exact step2_14
    · exact step2_15
  · change FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 2#usize
        {start:=16#usize,«end»:=16#usize} d2_16=ok (.done (.Ok value2))
    unfold FIo_Native.weights.partial_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=16#usize,«end»:=16#usize} : core.ops.range.Range Usize)=ok (none,{start:=16#usize,«end»:=16#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish2,bind_tc_ok]
#print axioms source2
end AspisR1.JGq_Partial
end
