import FJn_CopyWide
import FJk_CompositionWideOnRun
import R0P.SemDecision
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_LaneModel
abbrev E := AspisWideTower.WideExact
attribute [local irreducible] R0P.copyEvaluateWithSelectors R0P.copyActiveLiteral
  R0P.SemSource.scalarLaneAt R0P.poseidonPackedFamily
/-- The installed two-fold order is exactly the 29-lane model order. -/
theorem value (pub : R0P.Public E) (o : R0P.Openings E) (s : R0P.Sel E)
    (lambda chi theta h : E) :
    ExtractedMaskTerminalHorner.composeGroups theta
      (R0P.copyEvaluateWithSelectors o.z h (R0P.copySelectors s) lambda chi pub.nextPairIndex pub.variant).1
      (fun j=>R0P.pack4 ConcretePackBasis.basis (fun i=>R0P.SemSource.scalarLaneAt pub o s (4*j.val+i.val)))
      (fun j=>((R0P.poseidonPackedFamily ConcretePackBasis.basis).residuals pub o s).getD j.val 0)=
      ∑ i : Fin 29,theta^i.val*R0P.SemSource.laneAt pub lambda chi ConcretePackBasis.basis o h s i := by
  apply ExtractedMaskTerminalHorner.composeGroups_eq_lane_sum
  · intro i
    rw [R0P.SemSource.laneAt,if_pos (show (Fin.castAdd 25 i).val<4 from i.isLt)]
  · intro i
    rw [R0P.SemSource.laneAt,if_neg (show ¬(Fin.natAdd 4 (Fin.castAdd 1 i)).val<4 by omega),
      if_pos (show (Fin.natAdd 4 (Fin.castAdd 1 i)).val<28 by omega)]
    congr 2
  · rw [R0P.SemSource.laneAt,if_neg (by decide : ¬(28:Fin 29).val<4),
      if_neg (by decide : ¬(28:Fin 29).val<28)]
    rfl
#print axioms value
end AspisR1.FJn_LaneModel
end
