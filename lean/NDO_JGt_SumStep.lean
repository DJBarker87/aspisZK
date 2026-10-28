import NDO_JGt_ContractionStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGt_SumStep
open Aeneas Aeneas.Std Result ControlFlow
open JGt_ContractionStep (E)
theorem source (parts k : Array E 7#usize) (i next : Usize) (sum part power product value : E)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepUsize {start:=i,«end»:=7#usize} = ok (some i,{start:=next,«end»:=7#usize}))
    (read : Array.index_usize parts i=ok part) (kr : Array.index_usize k i=ok power)
    (mul : FIo_Native.aspis_core.field.wide_exact.WideExact.mul power part=ok product)
    (add : FIo_Native.aspis_core.field.wide_exact.WideExact.add sum product=ok value) :
    FIo_Native.weights.Weights.pair_loop9.body parts k {start:=i,«end»:=7#usize} sum=
      ok (.cont ({start:=next,«end»:=7#usize},value)) := by
  unfold FIo_Native.weights.Weights.pair_loop9.body
  rw [advance,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [read,bind_tc_ok]
  simp only [FIo_Native.trace.value,bind_tc_ok]
  rw [kr,bind_tc_ok,mul,bind_tc_ok,add,bind_tc_ok]
#print axioms source
end AspisR1.JGt_SumStep
end
