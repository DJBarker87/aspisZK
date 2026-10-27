import FJs_PreparedCircle
import FJs_FunctionalWeights
import FJs_DataFunctionals
import FJs_CircleRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_RowAlignment
open Aeneas Aeneas.Std Result AspisR1Stage2
open FJs_LiteralRows (K E P embed point)
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows

theorem weights (p : verifier.Prepared) (a : verifier.Accumulator) (parsed : OraclePortCompactDraft.Parsed)
    (data : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed data view)
        data.data (SelectedChallengeMap.rhoOf data.rho) q) am)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (matching : LiteralMatchingData.read rs=some data.data)
    (opening : LiteralOpeningView.read rs=some view)
    (range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0))
    (p0 p1 : P)
    (hz0 : Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 0#usize=ok p0)
    (hz1 : Array.index_usize (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) 1#usize=ok p1) :
    (fun i=>∑ j : Fin 7,data.data.kappa^j.val*FJr_PairRows.rows p.semantic_alpha p0 p1 j i)=
      FunctionalWeights.weights data.data.F data.data.F0 data.data.kappa := by
  have sem : SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)=fun j=>embed (point p.semantic_alpha j) := by
    funext j
    rw [FJs_PreparedPoint.point p a _ am fields j]
    exact (range j).symm
  have cz := FJs_PreparedCircle.coordinates p a _ am fields p0 p1 hz0 hz1
  have rz0 := FJs_CircleRange.view rs view opening 0
  have rz1 := FJs_CircleRange.view rs view opening 1
  have x0 : (view.circlePoints 0).val.1=embed (FJc_WeightValues.decode p0.x) := by
    rw [cz.1];exact rz0.1.symm
  have y0 : (view.circlePoints 0).val.2=embed (FJc_WeightValues.decode p0.y) := by
    rw [cz.2.1];exact rz0.2.symm
  have x1 : (view.circlePoints 1).val.1=embed (FJc_WeightValues.decode p1.x) := by
    rw [cz.2.2.1];exact rz1.1.symm
  have y1 : (view.circlePoints 1).val.2=embed (FJc_WeightValues.decode p1.y) := by
    rw [cz.2.2.2];exact rz1.2.symm
  have rows := FJs_FunctionalWeights.rows p.semantic_alpha p0 p1 _ _ sem x0 y0 x1 y1
  have weights := FJs_FunctionalWeights.weights p.semantic_alpha p0 p1 _ _ data.data.kappa rows
  have funcs := FJs_DataFunctionals.values rs data.data view matching opening
  rw [funcs.1,funcs.2]
  exact weights

#print axioms weights
end AspisR1.FJs_RowAlignment
end
