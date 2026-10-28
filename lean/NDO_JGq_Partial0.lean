import NDO_JGq_PartialPush0_0
import NDO_JGq_PartialPush0_1
import NDO_JGq_PartialPush0_2
import NDO_JGq_PartialPush0_3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish d0_16=ok value0 := by with_unfolding_all rfl
#print axioms finish0
theorem step0_0 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=0#usize,«end»:=16#usize} d0_0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},d0_1)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 0#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 0#usize=ok JGq_Common.c0 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 0#usize=ok (FIo_Install.toE JGo_TX2_Message00.value00) from JGo_TX2_Message00.native_field00,bind_tc_ok,
    read,bind_tc_ok,push0_0,bind_tc_ok]
  rfl
#print axioms step0_0
theorem step0_1 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=1#usize,«end»:=16#usize} d0_1=
    ok (.cont ({start:=2#usize,«end»:=16#usize},d0_2)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 1#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 1#usize=ok JGq_Common.c1 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 1#usize=ok (FIo_Install.toE JGo_TX2_Message00.value01) from JGo_TX2_Message00.native_field01,bind_tc_ok,
    read,bind_tc_ok,push0_1,bind_tc_ok]
  rfl
#print axioms step0_1
theorem step0_2 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=2#usize,«end»:=16#usize} d0_2=
    ok (.cont ({start:=3#usize,«end»:=16#usize},d0_3)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 2#usize=2#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 2#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 2#usize=ok JGq_Common.c2 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 2#usize=ok (FIo_Install.toE JGo_TX2_Message00.value02) from JGo_TX2_Message00.native_field02,bind_tc_ok,
    read,bind_tc_ok,push0_2,bind_tc_ok]
  rfl
#print axioms step0_2
theorem step0_3 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=3#usize,«end»:=16#usize} d0_3=
    ok (.cont ({start:=4#usize,«end»:=16#usize},d0_4)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 3#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 3#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 3#usize=ok JGq_Common.c3 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 3#usize=ok (FIo_Install.toE JGo_TX2_Message00.value03) from JGo_TX2_Message00.native_field03,bind_tc_ok,
    read,bind_tc_ok,push0_3,bind_tc_ok]
  rfl
#print axioms step0_3
theorem step0_4 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=4#usize,«end»:=16#usize} d0_4=
    ok (.cont ({start:=5#usize,«end»:=16#usize},d0_5)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 4#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 4#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 4#usize=ok JGq_Common.c4 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 4#usize 16#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 4#usize=ok (FIo_Install.toE JGo_TX2_Message00.value04) from JGo_TX2_Message00.native_field04,bind_tc_ok,
    read,bind_tc_ok,push0_4,bind_tc_ok]
  rfl
#print axioms step0_4
theorem step0_5 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=5#usize,«end»:=16#usize} d0_5=
    ok (.cont ({start:=6#usize,«end»:=16#usize},d0_6)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 5#usize=5#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 5#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 5#usize=ok JGq_Common.c5 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 5#usize 16#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 5#usize=ok (FIo_Install.toE JGo_TX2_Message00.value05) from JGo_TX2_Message00.native_field05,bind_tc_ok,
    read,bind_tc_ok,push0_5,bind_tc_ok]
  rfl
#print axioms step0_5
theorem step0_6 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=6#usize,«end»:=16#usize} d0_6=
    ok (.cont ({start:=7#usize,«end»:=16#usize},d0_7)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 6#usize=6#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 6#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 6#usize=ok JGq_Common.c6 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 6#usize 16#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 6#usize=ok (FIo_Install.toE JGo_TX2_Message00.value06) from JGo_TX2_Message00.native_field06,bind_tc_ok,
    read,bind_tc_ok,push0_6,bind_tc_ok]
  rfl
#print axioms step0_6
theorem step0_7 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=7#usize,«end»:=16#usize} d0_7=
    ok (.cont ({start:=8#usize,«end»:=16#usize},d0_8)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 7#usize=7#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 7#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 7#usize=ok JGq_Common.c7 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 7#usize 16#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 7#usize=ok (FIo_Install.toE JGo_TX2_Message00.value07) from JGo_TX2_Message00.native_field07,bind_tc_ok,
    read,bind_tc_ok,push0_7,bind_tc_ok]
  rfl
#print axioms step0_7
theorem step0_8 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=8#usize,«end»:=16#usize} d0_8=
    ok (.cont ({start:=9#usize,«end»:=16#usize},d0_9)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 8#usize=8#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 8#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 8#usize=ok JGq_Common.c8 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 8#usize 16#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 8#usize=ok (FIo_Install.toE JGo_TX2_Message08.value08) from JGo_TX2_Message08.native_field08,bind_tc_ok,
    read,bind_tc_ok,push0_8,bind_tc_ok]
  rfl
#print axioms step0_8
theorem step0_9 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=9#usize,«end»:=16#usize} d0_9=
    ok (.cont ({start:=10#usize,«end»:=16#usize},d0_10)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 9#usize=9#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 9#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 9#usize=ok JGq_Common.c9 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 9#usize 16#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 9#usize=ok (FIo_Install.toE JGo_TX2_Message08.value09) from JGo_TX2_Message08.native_field09,bind_tc_ok,
    read,bind_tc_ok,push0_9,bind_tc_ok]
  rfl
#print axioms step0_9
theorem step0_10 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=10#usize,«end»:=16#usize} d0_10=
    ok (.cont ({start:=11#usize,«end»:=16#usize},d0_11)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 10#usize=10#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 10#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 10#usize=ok JGq_Common.c10 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 10#usize 16#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 10#usize=ok (FIo_Install.toE JGo_TX2_Message08.value10) from JGo_TX2_Message08.native_field10,bind_tc_ok,
    read,bind_tc_ok,push0_10,bind_tc_ok]
  rfl
#print axioms step0_10
theorem step0_11 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=11#usize,«end»:=16#usize} d0_11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},d0_12)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 11#usize=11#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 11#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 11#usize=ok JGq_Common.c11 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 11#usize=ok (FIo_Install.toE JGo_TX2_Message08.value11) from JGo_TX2_Message08.native_field11,bind_tc_ok,
    read,bind_tc_ok,push0_11,bind_tc_ok]
  rfl
#print axioms step0_11
theorem step0_12 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=12#usize,«end»:=16#usize} d0_12=
    ok (.cont ({start:=13#usize,«end»:=16#usize},d0_13)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 12#usize=12#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 12#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 12#usize=ok JGq_Common.c12 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 12#usize 16#usize 13#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 12#usize=ok (FIo_Install.toE JGo_TX2_Message08.value12) from JGo_TX2_Message08.native_field12,bind_tc_ok,
    read,bind_tc_ok,push0_12,bind_tc_ok]
  rfl
#print axioms step0_12
theorem step0_13 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=13#usize,«end»:=16#usize} d0_13=
    ok (.cont ({start:=14#usize,«end»:=16#usize},d0_14)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 13#usize=13#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 13#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 13#usize=ok JGq_Common.c13 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 13#usize 16#usize 14#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 13#usize=ok (FIo_Install.toE JGo_TX2_Message08.value13) from JGo_TX2_Message08.native_field13,bind_tc_ok,
    read,bind_tc_ok,push0_13,bind_tc_ok]
  rfl
#print axioms step0_13
theorem step0_14 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=14#usize,«end»:=16#usize} d0_14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},d0_15)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 14#usize=14#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 14#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 14#usize=ok JGq_Common.c14 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 14#usize=ok (FIo_Install.toE JGo_TX2_Message08.value14) from JGo_TX2_Message08.native_field14,bind_tc_ok,
    read,bind_tc_ok,push0_14,bind_tc_ok]
  rfl
#print axioms step0_14
theorem step0_15 : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
    {start:=15#usize,«end»:=16#usize} d0_15=
    ok (.cont ({start:=16#usize,«end»:=16#usize},d0_16)) := by
  have mul : Usize.wrapping_mul 16#usize 0#usize=0#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize 0#usize (by decide))
  have add : Usize.wrapping_add 0#usize 15#usize=15#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 15#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 15#usize=ok JGq_Common.c15 := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next 15#usize 16#usize 16#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f 15#usize=ok (FIo_Install.toE JGo_TX2_Message08.value15) from JGo_TX2_Message08.native_field15,bind_tc_ok,
    read,bind_tc_ok,push0_15,bind_tc_ok]
  rfl
#print axioms step0_15
abbrev S0 := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states0 : Nat → S0
  | 0 => ({start:=0#usize,«end»:=16#usize},d0_0)
  | 1 => ({start:=1#usize,«end»:=16#usize},d0_1)
  | 2 => ({start:=2#usize,«end»:=16#usize},d0_2)
  | 3 => ({start:=3#usize,«end»:=16#usize},d0_3)
  | 4 => ({start:=4#usize,«end»:=16#usize},d0_4)
  | 5 => ({start:=5#usize,«end»:=16#usize},d0_5)
  | 6 => ({start:=6#usize,«end»:=16#usize},d0_6)
  | 7 => ({start:=7#usize,«end»:=16#usize},d0_7)
  | 8 => ({start:=8#usize,«end»:=16#usize},d0_8)
  | 9 => ({start:=9#usize,«end»:=16#usize},d0_9)
  | 10 => ({start:=10#usize,«end»:=16#usize},d0_10)
  | 11 => ({start:=11#usize,«end»:=16#usize},d0_11)
  | 12 => ({start:=12#usize,«end»:=16#usize},d0_12)
  | 13 => ({start:=13#usize,«end»:=16#usize},d0_13)
  | 14 => ({start:=14#usize,«end»:=16#usize},d0_14)
  | 15 => ({start:=15#usize,«end»:=16#usize},d0_15)
  | _ => ({start:=16#usize,«end»:=16#usize},d0_16)
theorem source0 : FIo_Native.weights.partial_dot f JGq_Common.a16 0#usize=ok (.Ok value0) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d0_0 := by rfl
  unfold FIo_Native.weights.partial_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.partial_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S0=>FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize x.1 x.2)
    states0 16 (.Ok value0)
  · intro i hi
    interval_cases i
    · exact step0_0
    · exact step0_1
    · exact step0_2
    · exact step0_3
    · exact step0_4
    · exact step0_5
    · exact step0_6
    · exact step0_7
    · exact step0_8
    · exact step0_9
    · exact step0_10
    · exact step0_11
    · exact step0_12
    · exact step0_13
    · exact step0_14
    · exact step0_15
  · change FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 0#usize
        {start:=16#usize,«end»:=16#usize} d0_16=ok (.done (.Ok value0))
    unfold FIo_Native.weights.partial_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({start:=16#usize,«end»:=16#usize} : core.ops.range.Range Usize)=ok (none,{start:=16#usize,«end»:=16#usize}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish0,bind_tc_ok]
#print axioms source0
end AspisR1.JGq_Partial
end
