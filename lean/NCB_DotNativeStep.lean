import NBS_NativeEight
set_option autoImplicit false
noncomputable section
namespace NCB_DotNativeStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
/-- Associate one native eight-cell observation with the SAME actual range,
scalar read, coefficient read and arbitrary sum prestate. No whole loop result
or successful dot output is a premise. -/
theorem source (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize)
    (slot : Usize) (iter : core.ops.range.Range Usize)
    (sums after : Array U64 8#usize) (wide : FIo_Install.NE)
    (coefficient : Array U32 8#usize) (scalar : U32) (n : Nat)
    (active : iter.start.val < iter.end.val)
    (scalarRead : JFr_TX2_ScalarRead.read q slot iter.start=ok scalar)
    (wideRead : Array.index_usize g iter.start=ok wide)
    (limbRead : FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs wide=ok coefficient)
    (hc : JFs_TX2_ArrayEight.Canon coefficient) (hscalar : scalar.val<2147483647)
    (hn : n<4) (hs : JFs_TX2_ArrayEight.Bound sums n)
    (observed : NBS_NativeEight.Observed coefficient scalar sums after) :
    ∃ next, next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
        ok (cont (next,after)) := by
  obtain ⟨⟨o,next⟩,step,ho,inc,ending⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro a b;rfl)
      iter active)
  subst o
  have cells := NBS_NativeEight.source coefficient scalar sums after n hc hscalar hn hs observed
  refine ⟨next,inc,ending,?_⟩
  rw [JFr_TX2_DotStep.body]
  simp only [JFr_TX2_DotStep.step,step,bind_tc_ok,Aeneas.Std.uncurry,scalarRead]
  rw [JFr_TX2_DotLanes.update]
  simp only [wideRead,limbRead,cells,bind_tc_ok]
#print axioms source
end NCB_DotNativeStep
end
