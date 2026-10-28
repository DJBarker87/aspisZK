import NCJ_TensorInnerTotal
import NCJ_ForwardRange
set_option autoImplicit false
noncomputable section
namespace NCJ_TensorOuterStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev W := FIo_Native.weights.Weights
abbrev Iter := core.ops.range.Range Usize
abbrev body := FIo_Native.weights.Weights.tensor_loop0.body

def Stage (d n : Nat) : Prop := (d=2 ∧ n=1) ∨ (d=3 ∧ n=4) ∨ (d=4 ∧ n=16) ∨ (d=5 ∧ n=64)
def Factors (w : W) : Prop := ∀ k (hk : k<5),∀ d (hd : d<5),NCJ_CellCanon.array
  (NCJ_GuardExact.pick (NCJ_GuardExact.pick w.factors k hk) d hd)

theorem active (w : W) (k n : Usize) (hk : k.val<5) (hf : Factors w)
    (iter : Iter) (he : iter.end.val=5) (stage : Stage iter.start.val n.val)
    (more : iter.start.val<5) (input : Slice NQ) (len : input.val.length=64)
    (ca : NCJ_CellCanon.slice input) :
    ∃ rest out next,body k iter w input n=ok (cont (rest,w,out,next)) ∧
      rest.start.val=iter.start.val+1 ∧ rest.end.val=5 ∧ Stage rest.start.val next.val ∧
      NCJ_CellCanon.slice out ∧ out.val.length=64 := by
  have hn : NCJ_TensorDomains.Stage n.val := by
    rcases stage with ⟨_,h⟩|⟨_,h⟩|⟨_,h⟩|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · omega
  obtain ⟨rest,advance,inc,last⟩ := NCJ_ForwardRange.active iter (by omega)
  obtain ⟨out,run,co,lo⟩ := NCJ_TensorInnerTotal.source w k iter.start n hk (by omega) hn
    (hf k.val hk iter.start.val (by omega)) n (by omega) input len ca
  have rev : core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
      {start:=0#usize,«end»:=n}=ok (NCJ_Reverse.cursor n) := by rfl
  let next := Usize.wrapping_mul n 4#usize
  have nv : next.val=n.val*4 := by
    dsimp [next,UScalar.wrapping_mul]
    rw [Nat.mod_eq_of_lt]
    rcases hn with h|h|h <;> rw [h] <;> scalar_tac
  refine ⟨rest,out,next,?_,inc,by omega,?_,co,lo⟩
  · simp only [body,NCJ_ForwardRange.next] at advance ⊢
    rw [advance]
    simp only [bind_tc_ok]
    dsimp! only
    rw [rev]
    simp only [bind_tc_ok]
    rw [run]
    rfl
  · rcases stage with ⟨d,n⟩|⟨d,n⟩|⟨d,n⟩|⟨d,_⟩
    · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega⟩))
    · omega

theorem done (w : W) (k n : Usize) (iter : Iter) (stop : iter.end.val≤iter.start.val)
    (input : Slice NQ) : body k iter w input n=ok (done input) := by
  have next:=NCJ_ForwardRange.done iter stop
  unfold NCJ_ForwardRange.next at next
  simp only [body,FIo_Native.weights.Weights.tensor_loop0.body,next,bind_tc_ok]
  rfl
#print axioms active
#print axioms done
end NCJ_TensorOuterStep
