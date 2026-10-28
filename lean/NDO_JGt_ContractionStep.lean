import NDO_JGq_PairShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_ContractionStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
theorem step8 (f : Slice U8) (libra : Array E 4#usize) (parts : Array E 7#usize)
    (i next : Usize) (old field weight product value : E)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepUsize {start:=i,«end»:=4#usize} = ok (some i,{start:=next,«end»:=4#usize}))
    (read : Array.index_usize parts 4#usize=ok old)
    (fr : FIo_Native.weights.field f i=ok field)
    (lr : Array.index_usize libra i=ok weight)
    (mul : FIo_Native.aspis_core.field.wide_exact.WideExact.mul field weight=ok product)
    (add : FIo_Native.aspis_core.field.wide_exact.WideExact.add old product=ok value) :
    FIo_Native.weights.Weights.pair_loop8.body f libra {start:=i,«end»:=4#usize} parts=
      ok (.cont ({start:=next,«end»:=4#usize},parts.set 4#usize value)) := by
  obtain ⟨a,ha,eq⟩ := WP.spec_imp_exists (Array.update_spec parts 4#usize value (by scalar_tac))
  subst a
  unfold FIo_Native.weights.Weights.pair_loop8.body
  rw [advance,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [read,bind_tc_ok,fr,bind_tc_ok,lr,bind_tc_ok,mul,bind_tc_ok,add,bind_tc_ok,ha,bind_tc_ok]
#print axioms step8
end AspisR1.JGt_ContractionStep
end
