import XRz_FinishValue
import XRz_FillCells
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishMaterialize
open XRx_FinishStep XRz_FinishLoop
def rowValue (b : verifier.BatchedWeights) (j : Nat) : Q :=
 if h : j<b.raw.length then XRz_FinishValue.newQ (S8OwnedP6Finish.modelValue b.raw.val[j])
 else ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
/-- Total materialization for every raw state, at the exact length domain. -/
theorem source (b : verifier.BatchedWeights) (w : Slice Q) (len : w.length≤b.raw.length) :
 ∃ out : Slice Q, verifier.BatchedWeights.finish b w=ok out ∧ out.length=w.length ∧
 ∀ j, j<w.length → out.val[j]?=some (rowValue b j) := by
 let initial : It := ⟨⟨w,0⟩,0#usize⟩
 have values : ∀ i : Usize, i.val<w.length → verifier.BatchedWeights.value b i=ok (rowValue b i.val) := by
  intro i hi
  rw [rowValue,dif_pos (by omega)]
  exact XRz_FinishValue.source b i (by omega)
 have run := XRz_FinishLoop.source b w (rowValue b) values w.length 0#usize id (by simp)
 let out := (fill (rowValue b) 0 w.length initial).iter.slice
 refine ⟨out,?_,XRz_FillCells.length _ _ _ _,?_⟩
 · unfold verifier.BatchedWeights.finish
   change (do let back ← verifier.BatchedWeights.finish_loop initial id b
              ok (back initial).iter.slice)=ok out
   rw [run]
   rfl
 · intro j hj
   exact (XRz_FillCells.cell (rowValue b) w.length 0 initial j hj).trans (if_pos (by omega))
#print axioms source
end XRz_FinishMaterialize
