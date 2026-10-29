import NDL_HighStep
import NDL_BoundedLoop
import NBQ_U06
set_option autoImplicit false
noncomputable section
namespace NDL_HighLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Iter := NDL_HighStep.Iter
abbrev Dot := NDL_HighStep.Dot
abbrev R := core.result.Result NE FIo_Native.verifier.Error

theorem total (p : Array NE 4#usize) (q : Array NQ 4#usize)
    (hp : ∀ x∈p.val,canonE x) (hq : NCJ_CellCanon.array q)
    (iter : Iter) (last : iter.end.val=4) (bound : iter.start.val≤4)
    (s : Dot) (count : s.count.val≤iter.start.val) :
    ∃ out,FIo_Native.weights.high_dot_loop iter p q s=ok (.Ok out) ∧ canonE out := by
  let step : Iter × Dot → Result (ControlFlow (Iter × Dot) R) :=
    fun t=>FIo_Native.weights.high_dot_loop.body p q t.1 t.2
  let inv : Iter → Dot → Prop := fun it dot=>dot.count.val≤it.start.val
  let post : R → Prop := fun r=>∃ out,r=.Ok out ∧ canonE out
  have active : ∀ it c,it.end.val=4 → it.start.val<it.end.val → inv it c →
      ∃ rest next,step (it,c)=ok (cont (rest,next)) ∧ rest.start.val=it.start.val+1 ∧
      rest.end.val=4 ∧ inv rest next := by
    intro it c ending more valid
    exact NDL_HighStep.active p q hp hq it ending more c valid
  have stopped : ∀ it c,it.end.val≤it.start.val → inv it c →
      ∃ out,step (it,c)=ok (done out) ∧ post out := by
    intro it c stop _
    obtain ⟨out,finish,canonical⟩ := NBQ_U06.finish c
    have next := NCJ_ForwardRange.done it stop
    unfold NCJ_ForwardRange.next at next
    exact ⟨.Ok out,by simp [step,FIo_Native.weights.high_dot_loop.body,next,finish],out,rfl,canonical⟩
  obtain ⟨result,run,out,equal,canonical⟩ :=
    NDL_BoundedLoop.total 4 step inv post active stopped iter s last bound count
  subst result
  exact ⟨out,run,canonical⟩

#print axioms total
end NDL_HighLoop
end
