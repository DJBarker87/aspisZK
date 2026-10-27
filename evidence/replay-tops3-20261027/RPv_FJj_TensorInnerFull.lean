import RPv_FJj_TensorInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorInnerFull
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
open FJa_ReverseStep (cursor)
open FJj_TensorModelAdvance (expanded)

theorem value (self selfOut : FIo_Native.weights.Weights) (k d n : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize self.factors k=ok row) (hd : Array.index_usize row d=ok digit)
    (hn : n.val≤16) (np : 0<n.val) (input out : Slice NQ)
    (hc : FJf_QMArray.canon digit) (hs : FJj_QMSlice.canon input)
    (run : FIo_Native.weights.Weights.tensor_loop0_loop0 (cursor n) self k input n d=ok (selfOut,out)) :
    selfOut=self ∧ FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧
      ∀ t,t<4*n.val → FJj_QMSlice.value out t=
        FJj_QMSlice.value input (t%n.val)*FJf_QMArray.value digit (t/n.val) := by
  have inv : ∀ t,FJj_QMSlice.value input t=
      expanded (FJj_QMSlice.value input) digit n.val n.val t := by
    intro t
    unfold expanded
    rw [if_neg (by have := Nat.mod_lt t np;omega)]
  have result := FJj_TensorInner.value self selfOut k d n n row digit hr hd hn (Nat.le_refl _)
    input out (FJj_QMSlice.value input) hc hs inv run
  refine ⟨result.1,result.2.1,result.2.2.1,?_⟩
  intro t ht
  rw [result.2.2.2 t,expanded,if_pos ⟨ht,Nat.zero_le _⟩]
#print axioms value
end AspisR1.FJj_TensorInnerFull
end
