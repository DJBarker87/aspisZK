import FJr_PairTrace
import FJr_CircleParts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_TraceCircles
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (cz : FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (kappa out : NE)
    (t : @FJr_PairTrace.Trace (FIo_Install.allocation r) (FIo_Install.toWeights w) alpha f kappa out)
    (halpha : ∀ x∈alpha.val,FIo_WideValues.Canon x) :
    letI := FIo_Install.allocation r;
    ∃ p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint,
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint z) 1#usize=ok p1 ∧
      FIp_ArrayValue.value t.parts 5=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
            (fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
              (FJc_WeightValues.decode p0.x) (FJc_WeightValues.decode p0.y) j.val)))) ∧
      FIp_ArrayValue.value t.parts 6=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide t.a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide t.a0))
            (fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
              (FJc_WeightValues.decode p1.x) (FJc_WeightValues.decode p1.y) j.val)))) := by
  letI := FIo_Install.allocation r
  have ca0 := FJc_SliceCanonical.read alpha 0#usize t.a0 halpha t.read0
  have ca1 := FJc_SliceCanonical.read alpha 1#usize t.a1 halpha t.read1
  have cs := FJm_Filled.canonical r 64#usize t.scratch t.filled
  obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := FJj_RegularTrace.reached (FIo_Install.toWeights w)
    alpha f 2#usize 64#usize t.ap0 t.ap1 t.scratch t.scratchOut _ t.regularParts t.regular
  have cs1 := FJr_KindTwoScratch.value r semAlpha z w hc hw alpha f t.ap0 t.ap1 t.scratch s1 _ p1 cs h2
  obtain ⟨point0,point1,hz0,hz1,cf,vf0,vf1⟩ := FJr_ConstructorCircleRows.value semAlpha z w hc cz hw
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  obtain ⟨row0,hr0⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 3#usize (by decide)
  obtain ⟨row1,hr1⟩ := FJj_ArrayReadTotal.value (FIo_Install.toWeights w).factors 4#usize (by decide)
  have nr0 := FJr_NativeRow.value w cf 3#usize row0 hr0
  have nr1 := FJr_NativeRow.value w cf 4#usize row1 hr1
  let factors0 : Fin 5 → Fin 4 → FK := fun d s=>FJr_CircleOuterCell.digit
    (FJc_WeightValues.decode point0.x) (FJc_WeightValues.decode point0.y) d.val s
  let factors1 : Fin 5 → Fin 4 → FK := fun d s=>FJr_CircleOuterCell.digit
    (FJc_WeightValues.decode point1.x) (FJc_WeightValues.decode point1.y) d.val s
  have rv0 : ∀ d s,FJj_TensorPrefix.rowValue row0 d.val s.val=factors0 d s := by
    intro d s
    exact (nr0.2 d.val s.val).trans (vf0 d s)
  have rv1 : ∀ d s,FJj_TensorPrefix.rowValue row1 d.val s.val=factors1 d s := by
    intro d s
    exact (nr1.2 d.val s.val).trans (vf1 d s)
  have v5 := FJr_RegularKindMeaning.value (FIo_Install.toWeights w) variant 5#usize 3#usize
    (by decide) FJr_KindIndices.five row0 hr0 nr0.1 factors0 rv0 alpha f
    t.a0 t.a1 t.ap0 t.ap1 ca0 ca1 t.powers0 t.powers1 s1 s2 p1 p2 cs1 h5
  have v6 := FJr_RegularKindMeaning.value (FIo_Install.toWeights w) variant 6#usize 4#usize
    (by decide) FJr_KindIndices.six row1 hr1 nr1.1 factors1 rv1 alpha f
    t.a0 t.a1 t.ap0 t.ap1 ca0 ca1 t.powers0 t.powers1 s2 t.scratchOut p2 t.regularParts v5.1 h6
  have tensor0 : FJd_PointReference.tensor (fun d s=>algebraMap FK FE (factors0 d s))=
      fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
        (FJc_WeightValues.decode point0.x) (FJc_WeightValues.decode point0.y) j.val) := by
    funext j
    exact FJr_CircleLiteral.mapped_tensor _ _ j
  have tensor1 : FJd_PointReference.tensor (fun d s=>algebraMap FK FE (factors1 d s))=
      fun j=>algebraMap FK FE (SelectedCircleWeightModel.circleWeight
        (FJc_WeightValues.decode point1.x) (FJc_WeightValues.decode point1.y) j.val) := by
    funext j
    exact FJr_CircleLiteral.mapped_tensor _ _ j
  rw [tensor0] at v5
  rw [tensor1] at v6
  have carry5 := FJj_RegularFrame.value (FIo_Install.toWeights w) 6#usize alpha f
    2#usize 64#usize t.ap0 t.ap1 s2 t.scratchOut p2 t.regularParts h6 5 (by decide)
  have shared5 := FJm_Continuation.shared (FIo_Install.toWeights w) t.commonPartials t.ap0 t.ap1 t.regularParts t.sharedParts t.sharedRun 5 (by decide) (by decide)
  have shared6 := FJm_Continuation.shared (FIo_Install.toWeights w) t.commonPartials t.ap0 t.ap1 t.regularParts t.sharedParts t.sharedRun 6 (by decide) (by decide)
  have tail5 := FJm_Continuation.tail f t.libra t.sharedParts t.lowParts t.parts t.inactive t.inactiveWrite t.libraWrite 5 (by decide) (by decide)
  have tail6 := FJm_Continuation.tail f t.libra t.sharedParts t.lowParts t.parts t.inactive t.inactiveWrite t.libraWrite 6 (by decide) (by decide)
  exact ⟨point0,point1,hz0,hz1,
    tail5.trans (shared5.trans (carry5.trans v5.2)),tail6.trans (shared6.trans v6.2)⟩

#print axioms value
end AspisR1.FJr_TraceCircles
end
