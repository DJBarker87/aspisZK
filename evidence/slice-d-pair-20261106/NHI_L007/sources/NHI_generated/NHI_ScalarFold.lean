import NHI_ScalarDomain
import NHI_ForwardRange
set_option autoImplicit false
namespace NHI_ScalarFold
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := core.ops.range.Range Usize
abbrev Closure := FIo_Native.weights.Weights.scalar_factor.closure
abbrev iterator := core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize
abbrev fnmut := FIo_Native.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact
abbrev body := FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body iterator fnmut
abbrev State := Iter × Closure × NE

def cells (p : Array NE 4#usize) (f : Array NQ 4#usize) : Nat → Usize → NE → Result NE
 | 0,_,v => ok v
 | fuel+1,s,v => do
  let (out,_) ← NHI_ScalarStep.step p f v s
  cells p f fuel (Usize.wrapping_add s 1#usize) out

theorem active (p : Array NE 4#usize) (f : Array NQ 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x)
 (v : NE) (hv : canonE v) (iter : Iter) (finish : iter.end.val=4)
 (more : iter.start.val<4) :
 ∃ rest out,body iter (p,f) v=ok (cont (rest,(p,f),out)) ∧
 NHI_ScalarStep.step p f v iter.start=ok (out,(p,f)) ∧
 rest.start.val=iter.start.val+1 ∧ rest.end.val=4 ∧ canonE out := by
 obtain ⟨rest,next,inc,last⟩ := NHI_ForwardRange.active iter (by omega)
 obtain ⟨out,call,co⟩ := NHI_ScalarDomain.total p f hp hf v hv iter.start more
 refine ⟨rest,out,?_,(NHI_ScalarStep.emitted p f v iter.start).trans call,inc,by rw [last];exact finish,co⟩
 unfold body FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body
 simp only [fnmut,iterator,core.iter.traits.iterator.IteratorRange]
 unfold NHI_ForwardRange.next at next
 rw [next]
 simp only [bind_tc_ok]
 dsimp! only
 rw [call]
 rfl

theorem done (iter : Iter) (v : NE) (c : Closure) (stop : iter.end.val ≤ iter.start.val) :
 body iter c v=ok (done v) := by
 have next := NHI_ForwardRange.done iter stop
 unfold NHI_ForwardRange.next at next
 simp only [body,FIo_Native.core.iter.traits.iterator.Iterator.fold.default_loop.body,
 iterator,core.iter.traits.iterator.IteratorRange,next,bind_tc_ok]
 rfl

/-- Complete finite emitted fold, SAME inputs and unchanged closure frame. -/
theorem finite (p : Array NE 4#usize) (f : Array NQ 4#usize)
 (hp : ∀ x∈p.val,canonE x) (hf : ∀ x∈f.val,canonQ x) (fuel : Nat)
 (iter : Iter) (last : iter.end.val=4) (remaining : fuel+iter.start.val=4)
 (v : NE) (hv : canonE v) :
 ∃ out,loop (fun t : State=>body t.1 t.2.1 t.2.2) (iter,(p,f),v)=ok out ∧
 cells p f fuel iter.start v=ok out ∧ canonE out := by
 induction fuel generalizing iter v with
 | zero =>
  refine ⟨v,?_,rfl,hv⟩
  rw [loop.eq_def,done iter v (p,f) (by omega)]
 | succ fuel ih =>
  obtain ⟨rest,next,run,cell,inc,finish,canonical⟩ := active p f hp hf v hv iter last (by omega)
  obtain ⟨out,fold,reference,co⟩ := ih rest finish (by omega) next canonical
  have small : iter.start.val+1<UScalar.size .Usize := by
   have cap : 4<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
   omega
  have same : Usize.wrapping_add iter.start 1#usize=rest.start := by
   apply UScalar.eq_of_val_eq
   rw [Usize.wrapping_add_val_eq]
   change (iter.start.val+1)%UScalar.size .Usize=rest.start.val
   rw [Nat.mod_eq_of_lt small,inc]
  refine ⟨out,?_,?_,co⟩
  · rw [loop.eq_def,run]
    exact fold
  · simp only [cells,cell,bind_tc_ok,same]
    exact reference

#print axioms active
#print axioms done
#print axioms finite
end NHI_ScalarFold
