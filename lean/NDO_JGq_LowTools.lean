import NDO_JGq_LowData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_LowTools
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE

theorem step (ap0 ap1 : Array E 4#usize) (iter cursor : core.ops.range.Range Usize)
    (before after : Array E 16#usize) (i d0 d1 p0 p1 : Usize)
    (x y product z : E) (m : U32)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some i,cursor))
    (rem : (i % 4#usize : Result Usize)=ok d0)
    (perm0 : Array.index_usize FIo_Native.weights.PERM d0=ok p0)
    (read0 : Array.index_usize ap0 p0=ok x)
    (quo : (i / 4#usize : Result Usize)=ok d1)
    (perm1 : Array.index_usize FIo_Native.weights.PERM d1=ok p1)
    (read1 : Array.index_usize ap1 p1=ok y)
    (multiply : FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok product)
    (quarter : FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER=ok m)
    (scale : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product m=ok z)
    (update : Array.update before i z=ok after) :
    FIo_Native.weights.Weights.pair_loop7.body ap0 ap1 iter before=ok (.cont (cursor,after)) := by
  unfold FIo_Native.weights.Weights.pair_loop7.body
  rw [next,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rem,bind_tc_ok,perm0,bind_tc_ok,read0,bind_tc_ok,quo,bind_tc_ok,perm1,bind_tc_ok,read1,bind_tc_ok,
    multiply,bind_tc_ok,quarter,bind_tc_ok,scale,bind_tc_ok,update,bind_tc_ok]
#print axioms step
end AspisR1.JGq_LowTools
end
