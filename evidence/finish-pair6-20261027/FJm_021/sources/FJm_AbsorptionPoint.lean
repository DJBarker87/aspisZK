import FJj_SuccessorCell
import FJf_ModelPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionPoint
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (decode)
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (alpha : Array SQ 10#usize) (points : FJf_PointBody.Points)
    (hc : FJc_WeightArray.canonical alpha)
    (run : FIn_WeightsExtract.state_only_prefix.r0.statement_points alpha=ok points) :
    ∃ absorption : Array SQ 10#usize,
      Array.index_usize points 2#usize=ok absorption ∧ FJc_WeightArray.canonical absorption ∧
      FJf_ModelPoint.decoded absorption=R0P.SemSource.xor12Point (FJf_ModelPoint.decoded alpha) := by
  unfold FIn_WeightsExtract.state_only_prefix.r0.statement_points
    FIn_WeightsExtract.state_only_prefix.state_only_statement_points at run
  obtain ⟨s,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨iter,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨successor,hsc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs,habs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨abs1,habs1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have cq := FJc_WeightArray.canonical_read alpha 7#usize q hc hq
  have vq := FJc_WeightArray.read alpha 7#usize q hq
  have v1 := FJc_WeightValues.sub _ q q1 FJc_WeightConstants.one.1 cq hq1
  have cabs := FJc_WeightArray.update alpha abs 7#usize q1 hc v1.1 habs
  have cq2 := FJc_WeightArray.canonical_read abs 6#usize q2 cabs hq2
  have vq2 := FJc_WeightArray.read abs 6#usize q2 hq2
  have v3 := FJc_WeightValues.sub _ q2 q3 FJc_WeightConstants.one.1 cq2 hq3
  refine ⟨abs1,rfl,FJc_WeightArray.update abs abs1 6#usize q3 cabs v3.1 habs1,?_⟩
  have q2eq : decode q2=FJc_WeightArray.value alpha 6 := by
    rw [←vq2,FJj_SuccessorCell.update alpha abs 7#usize q1 habs 6,if_neg (by decide)]
  funext j
  unfold FJf_ModelPoint.decoded R0P.SemSource.xor12Point
  rw [FJj_SuccessorCell.update abs abs1 6#usize q3 habs1 j.val,
    FJj_SuccessorCell.update alpha abs 7#usize q1 habs j.val,
    v3.2,v1.2,FJc_WeightConstants.one.2,q2eq,←vq]
  simp only [show (6#usize).val=6 from by decide,show (7#usize).val=7 from by decide]
  by_cases h6 : j.val=6
  · simp only [h6,if_true,eq_self,or_true]
  · by_cases h7 : j.val=7
    · simp only [h7,if_true,eq_self,true_or,show (6:Nat)≠7 from by decide,if_false]
    · simp only [h6,h7,Ne.symm h6,Ne.symm h7,if_false,or_self]
#print axioms value
end AspisR1.FJm_AbsorptionPoint
end
