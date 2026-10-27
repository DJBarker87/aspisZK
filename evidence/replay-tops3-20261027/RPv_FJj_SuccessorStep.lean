import RPv_FJj_SuccessorCell
import RPv_FJj_SuccessorModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorStep
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
open FJj_SuccessorCell (Rev next)
abbrev FK := OraclePortCheckpointAbiC5.K

def decoded (p : Array SQ 10#usize) : Fin 10 → FK := fun j=>FJc_WeightArray.value p j.val
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (z p out : Array SQ 10#usize) (carry carryOut : SQ)
    (iter cursor : Rev) (i : Usize) (hi : i.val<10)
    (hz : FJc_WeightArray.canonical z) (hp : FJc_WeightArray.canonical p) (hc : Canon carry)
    (hn : next iter=ok (some i,cursor))
    (run : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter p carry=
      ok (.cont (cursor,out,carryOut))) :
    FJc_WeightArray.canonical out ∧ Canon carryOut ∧
      (decode carryOut,decoded out)=FJd_LoopReference.successorStep (decoded z)
        (decode carry,decoded p) (FJj_SuccessorModel.index i.val) := by
  obtain ⟨co,cc,vc,vp⟩ := FJj_SuccessorCell.value z p out carry carryOut iter cursor i hz hp hc hn run
  have idx : FJj_SuccessorModel.index i.val=⟨i.val,hi⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  refine ⟨co,cc,?_⟩
  rw [idx]
  apply Prod.ext
  · exact vc
  · funext j
    unfold FJd_LoopReference.successorStep
    change FJc_WeightArray.value out j.val=Function.update (decoded p) ⟨i.val,hi⟩
      (decoded z ⟨i.val,hi⟩+decode carry-
        (decoded z ⟨i.val,hi⟩*decode carry+decoded z ⟨i.val,hi⟩*decode carry)) j
    rw [vp]
    by_cases h : i.val=j.val
    · have hj : j=⟨i.val,hi⟩ := Fin.ext h.symm
      subst j
      simp only [if_true,Function.update_self,decoded]
    · have hj : j≠⟨i.val,hi⟩ := by intro e;apply h;exact congrArg Fin.val e.symm
      simp only [h,if_false,Function.update_of_ne hj,decoded]
#print axioms value
end AspisR1.FJj_SuccessorStep
end
