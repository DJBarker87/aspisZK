import NCJ_ScalarCellTotal
import NCJ_ForwardRange
set_option autoImplicit false
noncomputable section
namespace NCJ_ScalarFoldStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := core.ops.range.Range Usize
abbrev Closure := NCJ_ScalarCellTotal.Closure
abbrev iterator := core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize
abbrev fnmut := FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
abbrev body := FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body iterator fnmut

theorem active (p : Array NE 4#usize) (f : Array NQ 4#usize) (hp : ∀ x∈p.val,canonE x)
    (v : NE) (hv : canonE v) (iter : Iter) (finish : iter.end.val=4)
    (more : iter.start.val< iter.end.val) :
    ∃ rest out,body iter (p,f) v=ok (cont (rest,(p,f),out)) ∧
      rest.start.val=iter.start.val+1 ∧ rest.end.val=4 ∧ canonE out := by
  obtain ⟨rest,next,inc,last⟩ := NCJ_ForwardRange.active iter more
  obtain ⟨out,call,co⟩ := NCJ_ScalarCellTotal.source p f hp v hv iter.start (by omega)
  refine ⟨rest,out,?_,inc,by rw [last];exact finish,co⟩
  unfold body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
  simp only [fnmut,iterator,core.iter.traits.iterator.IteratorRange]
  unfold NCJ_ForwardRange.next at next
  rw [next]
  simp only [bind_tc_ok]
  dsimp! only
  unfold NCJ_ScalarCellTotal.call at call
  rw [call]
  rfl

theorem done (iter : Iter) (v : NE) (c : Closure) (stop : iter.end.val≤ iter.start.val) :
    body iter c v=ok (done v) := by
  have next := NCJ_ForwardRange.done iter stop
  unfold NCJ_ForwardRange.next at next
  simp only [body,FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body,
    iterator,core.iter.traits.iterator.IteratorRange,next,bind_tc_ok]
  rfl

#print axioms active
#print axioms done
end NCJ_ScalarFoldStep
