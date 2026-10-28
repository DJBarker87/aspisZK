import NDO_JGq_LowData
import NDO_JGq_LowTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply4 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p0 JGq_Powers1.p3=ok product4 := by with_unfolding_all rfl
#print axioms multiply4
theorem scale4 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product4 134217728#u32=ok c4 := by with_unfolding_all rfl
#print axioms scale4
theorem step4 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=4#usize,«end»:=16#usize} a4=
    ok (.cont ({start:=5#usize,«end»:=16#usize},a5)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=4#usize,«end»:=16#usize} {start:=5#usize,«end»:=16#usize}
    a4 a5 4#usize 0#usize 1#usize 0#usize 3#usize
    JGq_Powers0.p0 JGq_Powers1.p3 product4 c4 134217728#u32
  · exact JGo_TX2_Range.next 4#usize 16#usize 5#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply4
  · with_unfolding_all rfl
  · exact scale4
  · rfl
#print axioms step4
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply5 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p3 JGq_Powers1.p3=ok product5 := by with_unfolding_all rfl
#print axioms multiply5
theorem scale5 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product5 134217728#u32=ok c5 := by with_unfolding_all rfl
#print axioms scale5
theorem step5 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=5#usize,«end»:=16#usize} a5=
    ok (.cont ({start:=6#usize,«end»:=16#usize},a6)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=5#usize,«end»:=16#usize} {start:=6#usize,«end»:=16#usize}
    a5 a6 5#usize 1#usize 1#usize 3#usize 3#usize
    JGq_Powers0.p3 JGq_Powers1.p3 product5 c5 134217728#u32
  · exact JGo_TX2_Range.next 5#usize 16#usize 6#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply5
  · with_unfolding_all rfl
  · exact scale5
  · rfl
#print axioms step5
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply6 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p2 JGq_Powers1.p3=ok product6 := by with_unfolding_all rfl
#print axioms multiply6
theorem scale6 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product6 134217728#u32=ok c6 := by with_unfolding_all rfl
#print axioms scale6
theorem step6 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=6#usize,«end»:=16#usize} a6=
    ok (.cont ({start:=7#usize,«end»:=16#usize},a7)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=6#usize,«end»:=16#usize} {start:=7#usize,«end»:=16#usize}
    a6 a7 6#usize 2#usize 1#usize 2#usize 3#usize
    JGq_Powers0.p2 JGq_Powers1.p3 product6 c6 134217728#u32
  · exact JGo_TX2_Range.next 6#usize 16#usize 7#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply6
  · with_unfolding_all rfl
  · exact scale6
  · rfl
#print axioms step6
end AspisR1.JGq_Low
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply7 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p1 JGq_Powers1.p3=ok product7 := by with_unfolding_all rfl
#print axioms multiply7
theorem scale7 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product7 134217728#u32=ok c7 := by with_unfolding_all rfl
#print axioms scale7
theorem step7 : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {start:=7#usize,«end»:=16#usize} a7=
    ok (.cont ({start:=8#usize,«end»:=16#usize},a8)) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {start:=7#usize,«end»:=16#usize} {start:=8#usize,«end»:=16#usize}
    a7 a8 7#usize 3#usize 1#usize 1#usize 3#usize
    JGq_Powers0.p1 JGq_Powers1.p3 product7 c7 134217728#u32
  · exact JGo_TX2_Range.next 7#usize 16#usize 8#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply7
  · with_unfolding_all rfl
  · exact scale7
  · rfl
#print axioms step7
end AspisR1.JGq_Low
end
