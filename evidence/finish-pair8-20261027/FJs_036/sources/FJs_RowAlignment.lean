import FJs_OperandAlignment
import FJs_PreparedCircle
import FJs_WideWeights
import FJs_ViewDirect
import FJs_DataFunctionals
import FJs_CircleRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_RowAlignment
open Aeneas Aeneas.Std Result AspisR1Stage2
open FJs_WideRows (K E P embed point)
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
  obtain ⟨sem,x0,y0,x1,y1⟩ := FJs_OperandAlignment.values p a parsed data view q am fields rs matching opening range p0 p1 hz0 hz1
  have rows := FJs_ViewDirect.rows p.semantic_alpha p0 p1 view sem x0 y0 x1 y1
  have weights : (fun i=>∑ j : Fin 7,data.data.kappa^j.val*FJr_PairRows.rows p.semantic_alpha p0 p1 j i)=
      FunctionalWeights.weights (SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact)
        (view.semantic.map Prod.snd) view.circlePoints)
        (SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact)
          (view.semantic.map Prod.snd) view.circlePoints) data.data.kappa := by
    rw [rows]
    funext i
    exact (RawFunctionalWeights.weights_eq_raw_rows (RingHom.id AspisWideTower.WideExact) _ data.data.kappa i).symm
  have funcs := FJs_DataFunctionals.values rs data.data view matching opening
  rw [funcs.1,funcs.2]
  exact weights

#print axioms weights
end AspisR1.FJs_RowAlignment
end
