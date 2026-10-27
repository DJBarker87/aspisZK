import FJr_ParsedPairMeaning
import FJr_Installation
import JGo_TX2_FinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

/-- Instantiates the inherited seven-part meaning at the actual retained TX2
operands. This is explicitly conditional meaning, not a forward Pair return. -/
theorem value (out : AspisR1Stage2.Stage2Finish.E)
    (run : FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
      (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint),
      Slice.index_usize (FIo_Install.toSlice JGo_TX2_FinishPrefix.alphas) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice JGo_TX2_FinishPrefix.alphas) 1#usize=ok a1 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint JFo_Prepared.value.z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint JFo_Prepared.value.z) 1#usize=ok p1 ∧
      CheckpointBytes5Output.ofE out=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field (JFw_Frames.window 8007 2048) i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun i=>∑ j : Fin 7,CheckpointBytes5Output.ofE JFo_Prepared.value.kappa^j.val*
              FJr_PairRows.rows JFo_Prepared.value.semantic_alpha p0 p1 j i))) := by
  have cz : FJr_CircleOuterCell.CanonZ
      (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint JFo_Prepared.value.z) := by
    rw [JGo_TX2_WeightData.z_pin]
    intro p hp
    change p∈[JGo_TX2_WeightData.z.val[0],JGo_TX2_WeightData.z.val[1]] at hp
    rcases List.mem_cons.mp hp with hp|hp
    · subst p
      change ((1922285720 < 2147483647 ∧ 1764102919 < 2147483647) ∧ (1090219375 < 2147483647 ∧ 1966128958 < 2147483647)) ∧ ((581146816 < 2147483647 ∧ 250060454 < 2147483647) ∧ (1903115135 < 2147483647 ∧ 1815951825 < 2147483647))
      decide
    · have he := List.mem_singleton.mp hp
      subst p
      change ((1598687308 < 2147483647 ∧ 1705339602 < 2147483647) ∧ (50113148 < 2147483647 ∧ 396595219 < 2147483647)) ∧ ((1362468980 < 2147483647 ∧ 298807548 < 2147483647) ∧ (913680565 < 2147483647 ∧ 2038915166 < 2147483647))
      decide
  have cp : ∀ x∈JFo_Prepared.value.alpha.val,FIo_WideValues.Canon (FIo_Install.toE x) := by
    intro x hx
    change x∈[JFq_Alpha0.scalar,JFq_Alpha1.scalar] at hx
    rcases List.mem_cons.mp hx with hx|hx
    · subst x
      exact FJg_ReaderScalarCanon.e _ _ _ JFq_Alpha0.source
    · have he := List.mem_singleton.mp hx
      subst x
      exact FJg_ReaderScalarCanon.e _ _ _ JFq_Alpha1.source
  exact FJr_ParsedPairMeaning.value (N:=2#usize) (.Ok ()) JFo_Prepared.value.semantic_alpha
    JFo_Prepared.value.z JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
    (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa out cz JGo_TX2_NewWeights.source
    (JFw_Frames.window_length 8007 2048 (by decide)) JFx_NativeBytes.checkpoint 408#usize 568#usize
    JFq_Semantic.native JFo_Prepared.value.alpha (by decide) cp (by rfl)
    (JFq_Raw.reader 208#usize) (JFq_Raw.reader 240#usize) JFq_Kappa.source run
#print axioms value
end AspisR1.JGq_PairMeaning
end
