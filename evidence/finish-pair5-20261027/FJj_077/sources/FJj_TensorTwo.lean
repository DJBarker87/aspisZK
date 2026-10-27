import FJj_TensorOuterLoop
import FJj_QMOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorTwo
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
open FJj_TensorOuterStep (Row Inv Post)

theorem value (self : FIo_Native.weights.Weights) (k : Usize) (row : Row)
    (hr : Array.index_usize self.factors k=ok row)
    (hc : ∀ digit∈row.val,FJf_QMArray.canon digit)
    (input out : Slice NQ) (hs : FJj_QMSlice.canon input)
    (run : FIo_Native.weights.Weights.tensor self k 2#usize input=ok out) :
    Post row input.val.length out := by
  unfold FIo_Native.weights.Weights.tensor at run
  obtain ⟨seeded,hseed,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have cs := FJj_QMSlice.update_canon input seeded 0#usize _ hs FJj_QMOne.canon hseed
  have len := FJj_QMSliceUpdate.length input seeded 0#usize _ hseed
  apply FJj_TensorOuterLoop.value self k row hr hc input.val.length
    {start:=2#usize,«end»:=5#usize} seeded out 1#usize _ run
  refine ⟨rfl,by change (2:Nat)≤2;omega,by change (2:Nat)≤5;omega,rfl,cs,len,rfl,?_⟩
  intro j hj
  have eq : j=0 := by change j<1 at hj;omega
  subst j
  rw [FJj_QMSliceUpdate.value input seeded 0#usize _ 0 hseed,if_pos (by rfl),FJj_QMOne.value]
  rfl
#print axioms value
end AspisR1.FJj_TensorTwo
end
