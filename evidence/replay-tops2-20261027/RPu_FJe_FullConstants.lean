import RPu_FJe_FullWeights
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_FullConstants
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
def even (l : State) (j : Fin (16#usize).val) : K :=
  decoded l ⟨1,by decide⟩*R0P.poseidonExternalInitial 2 j+
  decoded l ⟨9,by decide⟩*R0P.poseidonExternalFinal 0 j+
  decoded l ⟨10,by decide⟩*R0P.poseidonExternalFinal 2 j
def odd (l : State) (j : Fin (16#usize).val) : K :=
  decoded l ⟨1,by decide⟩*R0P.poseidonExternalInitial 3 j+
  decoded l ⟨9,by decide⟩*R0P.poseidonExternalFinal 1 j+
  decoded l ⟨10,by decide⟩*R0P.poseidonExternalFinal 3 j
/-- Exact even constants from the same selected weights and actual tables. -/
theorem even_value (l : State) (q0 q1 q2 : NQ) (out : State) (hl : canonical l)
    (r0 : Array.index_usize l 1#usize=ok q0)
    (r1 : Array.index_usize l 9#usize=ok q1)
    (r2 : Array.index_usize l 10#usize=ok q2)
    (run : state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [q0,q1,q2]) (FJb_InitialConstants.row 2)
      (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)=ok out) :
    canonical out ∧ decoded out=even l := by
  have w := FJe_FullWeights.value l q0 q1 q2 hl r0 r1 r2
  have v := FJe_ThreeColumns.value (FJe_FullWeights.weights q0 q1 q2)
    (FJb_InitialConstants.row 2) (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)
    out w.1 (FJb_InitialConstants.bounded 2)
    (FJe_FinalConstants.bounded 0) (FJe_FinalConstants.bounded 2) run
  refine ⟨v.1,v.2.trans ?_⟩
  funext j
  unfold FJe_ThreeColumnStep.model even
  rw [w.2.1,w.2.2.1,w.2.2.2,FJb_InitialConstants.model,FJe_FinalConstants.model,FJe_FinalConstants.model]
/-- Exact odd constants from those SAME weights and the other actual rows. -/
theorem odd_value (l : State) (q0 q1 q2 : NQ) (out : State) (hl : canonical l)
    (r0 : Array.index_usize l 1#usize=ok q0)
    (r1 : Array.index_usize l 9#usize=ok q1)
    (r2 : Array.index_usize l 10#usize=ok q2)
    (run : state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [q0,q1,q2]) (FJb_InitialConstants.row 3)
      (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)=ok out) :
    canonical out ∧ decoded out=odd l := by
  have w := FJe_FullWeights.value l q0 q1 q2 hl r0 r1 r2
  have v := FJe_ThreeColumns.value (FJe_FullWeights.weights q0 q1 q2)
    (FJb_InitialConstants.row 3) (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)
    out w.1 (FJb_InitialConstants.bounded 3)
    (FJe_FinalConstants.bounded 1) (FJe_FinalConstants.bounded 3) run
  refine ⟨v.1,v.2.trans ?_⟩
  funext j
  unfold FJe_ThreeColumnStep.model odd
  rw [w.2.1,w.2.2.1,w.2.2.2,FJb_InitialConstants.model,FJe_FinalConstants.model,FJe_FinalConstants.model]
#print axioms even_value
#print axioms odd_value
end AspisR1.FJe_FullConstants
end
