import NDO_JGq_PartialPush3_0
import NDO_JGq_PartialPush3_1
import NDO_JGq_PartialPush3_2
import NDO_JGq_PartialPush3_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish d3_16=ok value3 := by with_unfolding_all rfl
#print axioms finish3
theorem step3_0 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=0#usize,«end»:=16#usize} d3_0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},d3_1)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 0#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 0#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 0#usize=ok JGq_Common.c0 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 48#usize=ok (FIo_Install.toE JGo_TX2_Message48.value48) from JGo_TX2_Message48.native_field48,bind_tc_ok,
    read,bind_tc_ok,push3_0,bind_tc_ok]
  rfl
#print axioms step3_0
theorem step3_1 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=1#usize,«end»:=16#usize} d3_1=
    ok (.cont ({start:=2#usize,«end»:=16#usize},d3_2)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 1#usize=49#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 1#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 1#usize=ok JGq_Common.c1 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 49#usize=ok (FIo_Install.toE JGo_TX2_Message48.value49) from JGo_TX2_Message48.native_field49,bind_tc_ok,
    read,bind_tc_ok,push3_1,bind_tc_ok]
  rfl
#print axioms step3_1
theorem step3_2 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=2#usize,«end»:=16#usize} d3_2=
    ok (.cont ({start:=3#usize,«end»:=16#usize},d3_3)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 2#usize=50#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 2#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 2#usize=ok JGq_Common.c2 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 50#usize=ok (FIo_Install.toE JGo_TX2_Message48.value50) from JGo_TX2_Message48.native_field50,bind_tc_ok,
    read,bind_tc_ok,push3_2,bind_tc_ok]
  rfl
#print axioms step3_2
theorem step3_3 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=3#usize,«end»:=16#usize} d3_3=
    ok (.cont ({start:=4#usize,«end»:=16#usize},d3_4)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 3#usize=51#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 3#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 3#usize=ok JGq_Common.c3 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 51#usize=ok (FIo_Install.toE JGo_TX2_Message48.value51) from JGo_TX2_Message48.native_field51,bind_tc_ok,
    read,bind_tc_ok,push3_3,bind_tc_ok]
  rfl
#print axioms step3_3
theorem step3_4 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=4#usize,«end»:=16#usize} d3_4=
    ok (.cont ({start:=5#usize,«end»:=16#usize},d3_5)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 4#usize=52#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 4#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 4#usize=ok JGq_Common.c4 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 4#usize 16#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 52#usize=ok (FIo_Install.toE JGo_TX2_Message48.value52) from JGo_TX2_Message48.native_field52,bind_tc_ok,
    read,bind_tc_ok,push3_4,bind_tc_ok]
  rfl
#print axioms step3_4
theorem step3_5 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=5#usize,«end»:=16#usize} d3_5=
    ok (.cont ({start:=6#usize,«end»:=16#usize},d3_6)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 5#usize=53#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 5#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 5#usize=ok JGq_Common.c5 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 5#usize 16#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 53#usize=ok (FIo_Install.toE JGo_TX2_Message48.value53) from JGo_TX2_Message48.native_field53,bind_tc_ok,
    read,bind_tc_ok,push3_5,bind_tc_ok]
  rfl
#print axioms step3_5
theorem step3_6 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=6#usize,«end»:=16#usize} d3_6=
    ok (.cont ({start:=7#usize,«end»:=16#usize},d3_7)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 6#usize=54#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 6#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 6#usize=ok JGq_Common.c6 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 6#usize 16#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 54#usize=ok (FIo_Install.toE JGo_TX2_Message48.value54) from JGo_TX2_Message48.native_field54,bind_tc_ok,
    read,bind_tc_ok,push3_6,bind_tc_ok]
  rfl
#print axioms step3_6
theorem step3_7 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=7#usize,«end»:=16#usize} d3_7=
    ok (.cont ({start:=8#usize,«end»:=16#usize},d3_8)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 7#usize=55#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 7#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 7#usize=ok JGq_Common.c7 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 7#usize 16#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 55#usize=ok (FIo_Install.toE JGo_TX2_Message48.value55) from JGo_TX2_Message48.native_field55,bind_tc_ok,
    read,bind_tc_ok,push3_7,bind_tc_ok]
  rfl
#print axioms step3_7
theorem step3_8 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=8#usize,«end»:=16#usize} d3_8=
    ok (.cont ({start:=9#usize,«end»:=16#usize},d3_9)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 8#usize=56#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 8#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 8#usize=ok JGq_Common.c8 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 8#usize 16#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 56#usize=ok (FIo_Install.toE JGo_TX2_Message56.value56) from JGo_TX2_Message56.native_field56,bind_tc_ok,
    read,bind_tc_ok,push3_8,bind_tc_ok]
  rfl
#print axioms step3_8
theorem step3_9 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=9#usize,«end»:=16#usize} d3_9=
    ok (.cont ({start:=10#usize,«end»:=16#usize},d3_10)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 9#usize=57#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 9#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 9#usize=ok JGq_Common.c9 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 9#usize 16#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 57#usize=ok (FIo_Install.toE JGo_TX2_Message56.value57) from JGo_TX2_Message56.native_field57,bind_tc_ok,
    read,bind_tc_ok,push3_9,bind_tc_ok]
  rfl
#print axioms step3_9
theorem step3_10 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=10#usize,«end»:=16#usize} d3_10=
    ok (.cont ({start:=11#usize,«end»:=16#usize},d3_11)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 10#usize=58#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 10#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 10#usize=ok JGq_Common.c10 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 10#usize 16#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 58#usize=ok (FIo_Install.toE JGo_TX2_Message56.value58) from JGo_TX2_Message56.native_field58,bind_tc_ok,
    read,bind_tc_ok,push3_10,bind_tc_ok]
  rfl
#print axioms step3_10
theorem step3_11 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=11#usize,«end»:=16#usize} d3_11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},d3_12)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 11#usize=59#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 11#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 11#usize=ok JGq_Common.c11 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 59#usize=ok (FIo_Install.toE JGo_TX2_Message56.value59) from JGo_TX2_Message56.native_field59,bind_tc_ok,
    read,bind_tc_ok,push3_11,bind_tc_ok]
  rfl
#print axioms step3_11
theorem step3_12 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=12#usize,«end»:=16#usize} d3_12=
    ok (.cont ({start:=13#usize,«end»:=16#usize},d3_13)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 12#usize=60#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 12#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 12#usize=ok JGq_Common.c12 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 12#usize 16#usize 13#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 60#usize=ok (FIo_Install.toE JGo_TX2_Message56.value60) from JGo_TX2_Message56.native_field60,bind_tc_ok,
    read,bind_tc_ok,push3_12,bind_tc_ok]
  rfl
#print axioms step3_12
theorem step3_13 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=13#usize,«end»:=16#usize} d3_13=
    ok (.cont ({start:=14#usize,«end»:=16#usize},d3_14)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 13#usize=61#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 13#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 13#usize=ok JGq_Common.c13 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 13#usize 16#usize 14#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 61#usize=ok (FIo_Install.toE JGo_TX2_Message56.value61) from JGo_TX2_Message56.native_field61,bind_tc_ok,
    read,bind_tc_ok,push3_13,bind_tc_ok]
  rfl
#print axioms step3_13
theorem step3_14 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=14#usize,«end»:=16#usize} d3_14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},d3_15)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 14#usize=62#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 14#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 14#usize=ok JGq_Common.c14 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 62#usize=ok (FIo_Install.toE JGo_TX2_Message56.value62) from JGo_TX2_Message56.native_field62,bind_tc_ok,
    read,bind_tc_ok,push3_14,bind_tc_ok]
  rfl
#print axioms step3_14
theorem step3_15 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
    {start:=15#usize,«end»:=16#usize} d3_15=
    ok (.cont ({start:=16#usize,«end»:=16#usize},d3_16)) := by
  have mul : Usize.wrapping_mul 16#usize 3#usize=48#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 3#usize (by decide))
  have add : Usize.wrapping_add 48#usize 15#usize=63#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 48#usize 15#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 15#usize=ok JGq_Common.c15 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 15#usize 16#usize 16#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 63#usize=ok (FIo_Install.toE JGo_TX2_Message56.value63) from JGo_TX2_Message56.native_field63,bind_tc_ok,
    read,bind_tc_ok,push3_15,bind_tc_ok]
  rfl
#print axioms step3_15
abbrev S3 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states3 : Nat → S3
  | 0 => ({start:=0#usize,«end»:=16#usize},d3_0)
  | 1 => ({start:=1#usize,«end»:=16#usize},d3_1)
  | 2 => ({start:=2#usize,«end»:=16#usize},d3_2)
  | 3 => ({start:=3#usize,«end»:=16#usize},d3_3)
  | 4 => ({start:=4#usize,«end»:=16#usize},d3_4)
  | 5 => ({start:=5#usize,«end»:=16#usize},d3_5)
  | 6 => ({start:=6#usize,«end»:=16#usize},d3_6)
  | 7 => ({start:=7#usize,«end»:=16#usize},d3_7)
  | 8 => ({start:=8#usize,«end»:=16#usize},d3_8)
  | 9 => ({start:=9#usize,«end»:=16#usize},d3_9)
  | 10 => ({start:=10#usize,«end»:=16#usize},d3_10)
  | 11 => ({start:=11#usize,«end»:=16#usize},d3_11)
  | 12 => ({start:=12#usize,«end»:=16#usize},d3_12)
  | 13 => ({start:=13#usize,«end»:=16#usize},d3_13)
  | 14 => ({start:=14#usize,«end»:=16#usize},d3_14)
  | 15 => ({start:=15#usize,«end»:=16#usize},d3_15)
  | _ => ({start:=16#usize,«end»:=16#usize},d3_16)
theorem source3 : FIo_Native.weights.partial_dot f JGq_Common.a16 3#usize=ok (.Ok value3) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d3_0 := by rfl
  unfold FIo_Native.weights.partial_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.partial_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S3=>FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize x.1 x.2)
    states3 16 (.Ok value3)
  · intro i hi
    interval_cases i
    · exact step3_0
    · exact step3_1
    · exact step3_2
    · exact step3_3
    · exact step3_4
    · exact step3_5
    · exact step3_6
    · exact step3_7
    · exact step3_8
    · exact step3_9
    · exact step3_10
    · exact step3_11
    · exact step3_12
    · exact step3_13
    · exact step3_14
    · exact step3_15
  · change FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 3#usize
        {start:=16#usize,«end»:=16#usize} d3_16=ok (.done (.Ok value3))
    unfold FIo_Native.weights.partial_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=16#usize,«end»:=16#usize} : core.ops.range.Range Usize)=ok (none,{start:=16#usize,«end»:=16#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish3,bind_tc_ok]
#print axioms source3
end AspisR1.JGq_Partial
end
