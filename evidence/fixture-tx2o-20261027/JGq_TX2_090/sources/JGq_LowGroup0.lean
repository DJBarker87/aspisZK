import JGq_LowData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p0 JGq_Powers1.p0=ok product0 := by with_unfolding_all rfl
#print axioms multiply0
theorem scale0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product0 134217728#u32=ok c0 := by with_unfolding_all rfl
#print axioms scale0
theorem step0 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=0#usize,«end»:=16#usize} a0=
    ok (.cont ({start:=1#usize,«end»:=16#usize},a1)) := by
  unfold FIo_Native.weights.Weights.pair_loop7.body
  rw [JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide),bind_tc_ok]
  have rem : (0#usize % 4#usize : Result Usize)=ok 0#usize := by rfl
  have quo : (0#usize / 4#usize : Result Usize)=ok 0#usize := by rfl
  have perm0 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have perm1 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have read0 : Array.index_usize JGq_Powers0.a4 0#usize=ok JGq_Powers0.p0 := by rfl
  have read1 : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have quarter : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok 134217728#u32 := by with_unfolding_all rfl
  simp only [Aeneas.Std.uncurry]
  rw [rem,bind_tc_ok,perm0,bind_tc_ok,read0,bind_tc_ok,quo,bind_tc_ok,perm1,bind_tc_ok,read1,bind_tc_ok,
    multiply0,bind_tc_ok,quarter,bind_tc_ok,scale0,bind_tc_ok]
  rfl
#print axioms step0
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p3 JGq_Powers1.p0=ok product1 := by with_unfolding_all rfl
#print axioms multiply1
theorem scale1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product1 134217728#u32=ok c1 := by with_unfolding_all rfl
#print axioms scale1
theorem step1 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=1#usize,«end»:=16#usize} a1=
    ok (.cont ({start:=2#usize,«end»:=16#usize},a2)) := by
  unfold FIo_Native.weights.Weights.pair_loop7.body
  rw [JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide),bind_tc_ok]
  have rem : (1#usize % 4#usize : Result Usize)=ok 1#usize := by rfl
  have quo : (1#usize / 4#usize : Result Usize)=ok 0#usize := by rfl
  have perm0 : Array.index_usize FIo_Native.weights.PERM 1#usize=ok 3#usize := by with_unfolding_all rfl
  have perm1 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have read0 : Array.index_usize JGq_Powers0.a4 3#usize=ok JGq_Powers0.p3 := by rfl
  have read1 : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have quarter : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok 134217728#u32 := by with_unfolding_all rfl
  simp only [Aeneas.Std.uncurry]
  rw [rem,bind_tc_ok,perm0,bind_tc_ok,read0,bind_tc_ok,quo,bind_tc_ok,perm1,bind_tc_ok,read1,bind_tc_ok,
    multiply1,bind_tc_ok,quarter,bind_tc_ok,scale1,bind_tc_ok]
  rfl
#print axioms step1
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p2 JGq_Powers1.p0=ok product2 := by with_unfolding_all rfl
#print axioms multiply2
theorem scale2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product2 134217728#u32=ok c2 := by with_unfolding_all rfl
#print axioms scale2
theorem step2 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=2#usize,«end»:=16#usize} a2=
    ok (.cont ({start:=3#usize,«end»:=16#usize},a3)) := by
  unfold FIo_Native.weights.Weights.pair_loop7.body
  rw [JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide),bind_tc_ok]
  have rem : (2#usize % 4#usize : Result Usize)=ok 2#usize := by rfl
  have quo : (2#usize / 4#usize : Result Usize)=ok 0#usize := by rfl
  have perm0 : Array.index_usize FIo_Native.weights.PERM 2#usize=ok 2#usize := by with_unfolding_all rfl
  have perm1 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have read0 : Array.index_usize JGq_Powers0.a4 2#usize=ok JGq_Powers0.p2 := by rfl
  have read1 : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have quarter : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok 134217728#u32 := by with_unfolding_all rfl
  simp only [Aeneas.Std.uncurry]
  rw [rem,bind_tc_ok,perm0,bind_tc_ok,read0,bind_tc_ok,quo,bind_tc_ok,perm1,bind_tc_ok,read1,bind_tc_ok,
    multiply2,bind_tc_ok,quarter,bind_tc_ok,scale2,bind_tc_ok]
  rfl
#print axioms step2
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply3 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p1 JGq_Powers1.p0=ok product3 := by with_unfolding_all rfl
#print axioms multiply3
theorem scale3 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product3 134217728#u32=ok c3 := by with_unfolding_all rfl
#print axioms scale3
theorem step3 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=3#usize,«end»:=16#usize} a3=
    ok (.cont ({start:=4#usize,«end»:=16#usize},a4)) := by
  unfold FIo_Native.weights.Weights.pair_loop7.body
  rw [JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide),bind_tc_ok]
  have rem : (3#usize % 4#usize : Result Usize)=ok 3#usize := by rfl
  have quo : (3#usize / 4#usize : Result Usize)=ok 0#usize := by rfl
  have perm0 : Array.index_usize FIo_Native.weights.PERM 3#usize=ok 1#usize := by with_unfolding_all rfl
  have perm1 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have read0 : Array.index_usize JGq_Powers0.a4 1#usize=ok JGq_Powers0.p1 := by rfl
  have read1 : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have quarter : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok 134217728#u32 := by with_unfolding_all rfl
  simp only [Aeneas.Std.uncurry]
  rw [rem,bind_tc_ok,perm0,bind_tc_ok,read0,bind_tc_ok,quo,bind_tc_ok,perm1,bind_tc_ok,read1,bind_tc_ok,
    multiply3,bind_tc_ok,quarter,bind_tc_ok,scale3,bind_tc_ok]
  rfl
#print axioms step3
end AspisR1.JGq_Low
end
