import NDO_JGq_LowData
import NDO_JGq_LowTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply8 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p0 JGq_Powers1.p2=ok product8 := by with_unfolding_all rfl
#print axioms multiply8
theorem scale8 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product8 134217728#u32=ok c8 := by with_unfolding_all rfl
#print axioms scale8
theorem step8 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=8#usize,«end»:=16#usize} a8=
    ok (.cont ({start:=9#usize,«end»:=16#usize},a9)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=8#usize,«end»:=16#usize} {start:=9#usize,«end»:=16#usize}
    a8 a9 8#usize 0#usize 2#usize 0#usize 2#usize
    JGq_Powers0.p0 JGq_Powers1.p2 product8 c8 134217728#u32
  · exact JGo_TX2_Range.next 8#usize 16#usize 9#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply8
  · with_unfolding_all rfl
  · exact scale8
  · rfl
#print axioms step8
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply9 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p3 JGq_Powers1.p2=ok product9 := by with_unfolding_all rfl
#print axioms multiply9
theorem scale9 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product9 134217728#u32=ok c9 := by with_unfolding_all rfl
#print axioms scale9
theorem step9 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=9#usize,«end»:=16#usize} a9=
    ok (.cont ({start:=10#usize,«end»:=16#usize},a10)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=9#usize,«end»:=16#usize} {start:=10#usize,«end»:=16#usize}
    a9 a10 9#usize 1#usize 2#usize 3#usize 2#usize
    JGq_Powers0.p3 JGq_Powers1.p2 product9 c9 134217728#u32
  · exact JGo_TX2_Range.next 9#usize 16#usize 10#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply9
  · with_unfolding_all rfl
  · exact scale9
  · rfl
#print axioms step9
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply10 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p2 JGq_Powers1.p2=ok product10 := by with_unfolding_all rfl
#print axioms multiply10
theorem scale10 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product10 134217728#u32=ok c10 := by with_unfolding_all rfl
#print axioms scale10
theorem step10 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=10#usize,«end»:=16#usize} a10=
    ok (.cont ({start:=11#usize,«end»:=16#usize},a11)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=10#usize,«end»:=16#usize} {start:=11#usize,«end»:=16#usize}
    a10 a11 10#usize 2#usize 2#usize 2#usize 2#usize
    JGq_Powers0.p2 JGq_Powers1.p2 product10 c10 134217728#u32
  · exact JGo_TX2_Range.next 10#usize 16#usize 11#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply10
  · with_unfolding_all rfl
  · exact scale10
  · rfl
#print axioms step10
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply11 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p1 JGq_Powers1.p2=ok product11 := by with_unfolding_all rfl
#print axioms multiply11
theorem scale11 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product11 134217728#u32=ok c11 := by with_unfolding_all rfl
#print axioms scale11
theorem step11 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=11#usize,«end»:=16#usize} a11=
    ok (.cont ({start:=12#usize,«end»:=16#usize},a12)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=11#usize,«end»:=16#usize} {start:=12#usize,«end»:=16#usize}
    a11 a12 11#usize 3#usize 2#usize 1#usize 2#usize
    JGq_Powers0.p1 JGq_Powers1.p2 product11 c11 134217728#u32
  · exact JGo_TX2_Range.next 11#usize 16#usize 12#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply11
  · with_unfolding_all rfl
  · exact scale11
  · rfl
#print axioms step11
end AspisR1.JGq_Low
end
