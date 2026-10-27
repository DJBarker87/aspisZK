import RPu_FJa_InclusiveSteps
set_option autoImplicit false
namespace AspisR1.FJa_InclusiveFoldStep
open Aeneas Aeneas.Std Result FIq_Native
/-- One symbolic unfolding, guarded by the already checked iterator step. -/
theorem step {Acc F : Type} (fn : core.ops.function.FnMut F (Acc × Usize) Acc)
    (it tail : FJa_InclusiveNext.Range) (x : Usize)
    (hn : FJa_InclusiveNext.next it=ok (some x,tail)) (acc : Acc) (f : F) :
    rangeFold core.iter.range.StepUsize fn it acc f=(do
      let (acc',f')←fn.call_mut f (acc,x)
      rangeFold core.iter.range.StepUsize fn tail acc' f') := by
  unfold FJa_InclusiveNext.next at hn
  rw [rangeFold.eq_def,hn]
  rfl
theorem stop {Acc F : Type} (fn : core.ops.function.FnMut F (Acc × Usize) Acc)
    (it : FJa_InclusiveNext.Range)
    (hn : FJa_InclusiveNext.next it=ok (none,it)) (acc : Acc) (f : F) :
    rangeFold core.iter.range.StepUsize fn it acc f=ok acc := by
  unfold FJa_InclusiveNext.next at hn
  rw [rangeFold.eq_def,hn]
  rfl
#print axioms step
#print axioms stop
end AspisR1.FJa_InclusiveFoldStep
