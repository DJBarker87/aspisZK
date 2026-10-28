import NDO_JGq_LowData
import NDO_JGq_LowTools
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
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=0#usize,«end»:=16#usize} {start:=1#usize,«end»:=16#usize}
    a0 a1 0#usize 0#usize 0#usize 0#usize 0#usize
    JGq_Powers0.p0 JGq_Powers1.p0 product0 c0 134217728#u32
  · exact JGo_TX2_Range.next 0#usize 16#usize 1#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply0
  · with_unfolding_all rfl
  · exact scale0
  · rfl
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
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=1#usize,«end»:=16#usize} {start:=2#usize,«end»:=16#usize}
    a1 a2 1#usize 1#usize 0#usize 3#usize 0#usize
    JGq_Powers0.p3 JGq_Powers1.p0 product1 c1 134217728#u32
  · exact JGo_TX2_Range.next 1#usize 16#usize 2#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply1
  · with_unfolding_all rfl
  · exact scale1
  · rfl
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
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=2#usize,«end»:=16#usize} {start:=3#usize,«end»:=16#usize}
    a2 a3 2#usize 2#usize 0#usize 2#usize 0#usize
    JGq_Powers0.p2 JGq_Powers1.p0 product2 c2 134217728#u32
  · exact JGo_TX2_Range.next 2#usize 16#usize 3#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply2
  · with_unfolding_all rfl
  · exact scale2
  · rfl
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
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=3#usize,«end»:=16#usize} {start:=4#usize,«end»:=16#usize}
    a3 a4 3#usize 3#usize 0#usize 1#usize 0#usize
    JGq_Powers0.p1 JGq_Powers1.p0 product3 c3 134217728#u32
  · exact JGo_TX2_Range.next 3#usize 16#usize 4#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply3
  · with_unfolding_all rfl
  · exact scale3
  · rfl
#print axioms step3
end AspisR1.JGq_Low
end
