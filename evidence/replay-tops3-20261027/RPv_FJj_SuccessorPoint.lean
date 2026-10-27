import RPv_FJj_SuccessorCut
import RPv_FJj_SuccessorLoop
import RPv_FJj_SuccessorLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorPoint
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJj_SuccessorStep (decoded)

theorem value (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points) :
    ∃ successor : Array SQ 10#usize,
      Array.index_usize points 1#usize=ok successor ∧ FJc_WeightArray.canonical successor ∧
      decoded successor=R0P.SemSource.successorPoint (decoded alpha) := by
  obtain ⟨iter,successor,hi,hsc,hp⟩ := FJj_SuccessorCut.value alpha points run
  have len : Slice.len (Array.to_slice alpha)=10#usize := by scalar_tac
  rw [len] at hi
  have ei : iter=FJa_ReverseStep.cursor 10#usize := (Result.ok.inj hi).symm
  subst iter
  have value := FJj_SuccessorLoop.value alpha alpha successor FIn_WeightsExtract.field.QM31.ONE
    10#usize (by change (10:Nat)≤10;omega) hc hc FJc_WeightConstants.one.1 hsc
  refine ⟨successor,hp,value.1,?_⟩
  rw [value.2,FJc_WeightConstants.one.2]
  exact FJj_SuccessorLiteral.value (decoded alpha)
#print axioms value
end AspisR1.FJj_SuccessorPoint
end
