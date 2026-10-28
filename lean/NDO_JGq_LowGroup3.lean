import NDO_JGq_LowData
import NDO_JGq_LowTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply12 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p0 JGq_Powers1.p1=ok product12 := by with_unfolding_all rfl
#print axioms multiply12
theorem scale12 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product12 134217728#u32=ok c12 := by with_unfolding_all rfl
#print axioms scale12
theorem step12 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=12#usize,«end»:=16#usize} a12=
    ok (.cont ({start:=13#usize,«end»:=16#usize},a13)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=12#usize,«end»:=16#usize} {start:=13#usize,«end»:=16#usize}
    a12 a13 12#usize 0#usize 3#usize 0#usize 1#usize
    JGq_Powers0.p0 JGq_Powers1.p1 product12 c12 134217728#u32
  · exact JGo_TX2_Range.next 12#usize 16#usize 13#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply12
  · with_unfolding_all rfl
  · exact scale12
  · rfl
#print axioms step12
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply13 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p3 JGq_Powers1.p1=ok product13 := by with_unfolding_all rfl
#print axioms multiply13
theorem scale13 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product13 134217728#u32=ok c13 := by with_unfolding_all rfl
#print axioms scale13
theorem step13 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=13#usize,«end»:=16#usize} a13=
    ok (.cont ({start:=14#usize,«end»:=16#usize},a14)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=13#usize,«end»:=16#usize} {start:=14#usize,«end»:=16#usize}
    a13 a14 13#usize 1#usize 3#usize 3#usize 1#usize
    JGq_Powers0.p3 JGq_Powers1.p1 product13 c13 134217728#u32
  · exact JGo_TX2_Range.next 13#usize 16#usize 14#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply13
  · with_unfolding_all rfl
  · exact scale13
  · rfl
#print axioms step13
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply14 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p2 JGq_Powers1.p1=ok product14 := by with_unfolding_all rfl
#print axioms multiply14
theorem scale14 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product14 134217728#u32=ok c14 := by with_unfolding_all rfl
#print axioms scale14
theorem step14 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=14#usize,«end»:=16#usize} a14=
    ok (.cont ({start:=15#usize,«end»:=16#usize},a15)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=14#usize,«end»:=16#usize} {start:=15#usize,«end»:=16#usize}
    a14 a15 14#usize 2#usize 3#usize 2#usize 1#usize
    JGq_Powers0.p2 JGq_Powers1.p1 product14 c14 134217728#u32
  · exact JGo_TX2_Range.next 14#usize 16#usize 15#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply14
  · with_unfolding_all rfl
  · exact scale14
  · rfl
#print axioms step14
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply15 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p1 JGq_Powers1.p1=ok product15 := by with_unfolding_all rfl
#print axioms multiply15
theorem scale15 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product15 134217728#u32=ok c15 := by with_unfolding_all rfl
#print axioms scale15
theorem step15 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=15#usize,«end»:=16#usize} a15=
    ok (.cont ({start:=16#usize,«end»:=16#usize},a16)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=15#usize,«end»:=16#usize} {start:=16#usize,«end»:=16#usize}
    a15 a16 15#usize 3#usize 3#usize 1#usize 1#usize
    JGq_Powers0.p1 JGq_Powers1.p1 product15 c15 134217728#u32
  · exact JGo_TX2_Range.next 15#usize 16#usize 16#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply15
  · with_unfolding_all rfl
  · exact scale15
  · rfl
#print axioms step15
end AspisR1.JGq_Low
end
