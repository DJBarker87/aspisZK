import RPv_FJr_PairMeaning
import RPv_FJr_PreparedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_BodyPairMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv

theorem value (r : NP6_StdModel.Reservation) (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am)
    (w : FIo_Install.W) (alpha : Slice AspisR1Stage2.Stage2Finish.E) (f : Slice U8)
    (out : AspisR1Stage2.Stage2Finish.E)
    (hw : FIn_WeightsInstall.newWeights p.variant p.semantic_alpha p.z=ok (.Ok w))
    (prefixRun : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1Stage2.Stage2Finish.E)) p.alpha ⟨2#usize⟩=ok alpha)
    (len : f.val.length=2048)
    (run : FIo_Install.pair r w alpha f p.kappa=ok (.Ok out)) :
    ∃ (a0 a1 : NE) (p0 p1 : FIn_WeightsExtract.circle.SecureCirclePoint),
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 0#usize=ok p0 ∧
      Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 1#usize=ok p1 ∧
      CheckpointBytes5Output.ofE out=RoundPairing.dot
        (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
            (fun i=>∑ j : Fin 7,CheckpointBytes5Output.ofE p.kappa^j.val*FJr_PairRows.rows p.semantic_alpha p0 p1 j i))) := by
  have canon := FJr_PreparedCanonical.value p a pm am fields
  have shape := FJr_AlphaPrefix.value p.alpha alpha (by decide) prefixRun
  have halpha := FJr_AlphaPrefix.canonical p.alpha alpha (by decide) canon.2.2.1 prefixRun
  rw [fields.variant] at hw
  exact FJr_PairMeaning.value r p.semantic_alpha p.z w alpha f p.kappa out canon.1 canon.2.1 hw shape.2 len halpha canon.2.2.2 run

#print axioms value
end AspisR1.FJr_BodyPairMeaning
end
