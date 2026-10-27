import FJb_MatrixBlockLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixBlock
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
theorem value (s out : State) (g : Usize) (hg : g.val < 4)
    (hs : canonical s) (run : block s g=ok out) :
    canonical out ∧ decoded out=model s g.val := by
  obtain ⟨i0,i1,i2,i3,next,h0,v0,h1,v1,h2,v2,h3,v3,_,_⟩ := FJb_GroupIndices.value g hg
  rw [factor s g i0 i1 i2 i3 h0 h1 h2 h3] at run
  have b0 : i0.val < (16#usize).val := by change i0.val < 16;omega
  have b1 : i1.val < (16#usize).val := by change i1.val < 16;omega
  have b2 : i2.val < (16#usize).val := by change i2.val < 16;omega
  have b3 : i3.val < (16#usize).val := by change i3.val < 16;omega
  have v := FJb_MatrixGroupStep.value s out i0 i1 i2 i3 b0 b1 b2 b3 hs run
  have hi : FJb_MatrixGroupStep.inputs s i0 i1 i2 i3=input s g.val := by
    funext k
    fin_cases k <;> simp only [FJb_MatrixGroupStep.inputs,input,v0,v1,v2,v3,Nat.add_zero]
  refine ⟨v.1,?_⟩
  rw [v.2]
  unfold FJb_MatrixGroupStep.model
  rw [hi]
  funext j
  simp only [model,Function.update_apply,Fin.ext_iff,v0,v1,v2,v3]
#print axioms value
end AspisR1.FJb_MatrixBlock
end
