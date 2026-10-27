import FJs_FunctionalWeights
import FJs_PreparedCircle
import FJs_PreparedAlphas
import FJs_FinalMessage
import FJs_DataFunctionals
import FJs_CircleRange
import FIn_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_LiteralPair
open Aeneas Aeneas.Std Result AspisR1Stage2
open FJs_LiteralRows (K E P embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows

theorem value (r : NP6_StdModel.Reservation) (seed : Stage2Finish.FinishOps FIo_Install.W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (parsed : OraclePortCompactDraft.Parsed)
    (data : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144) (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed data view)
        data.data (SelectedChallengeMap.rhoOf data.rho) q) am)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (matching : LiteralMatchingData.read rs=some data.data)
    (opening : LiteralOpeningView.read rs=some view)
    (range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0))
    (encoded : SelectedFieldSequenceCodec.encodeWide data.data.f=MultiproofConeCanonical.bytesOf v.final_message.val) :
    FIn_Finish.PairMeaning (FIo_Install.finishOps r seed) v p data.data := by
  intro w alpha out hw hp run
  obtain ⟨a0,a1,p0,p1,h0,h1,hz0,hz1,body⟩ := FJr_BodyPairMeaning.value r p a _ am fields w alpha v.final_message out
    hw hp (FJs_FinalMessage.length _ _ encoded) run
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
  have alphas := FJs_PreparedAlphas.values p a _ am fields alpha hp a0 a1 h0 h1
  have kappa : CheckpointBytes5Output.ofE p.kappa=data.data.kappa := by
    rw [fields.kappa,CheckpointBytes5Output.ofE_source];rfl
  rw [FJs_FinalMessage.value _ _ encoded,kappa,alphas.1,alphas.2] at body
  change CheckpointBytes5Output.ofE out=RoundPairing.dot data.data.f
    (RoundPairing.dualFold (n:=64) data.data.alpha1 (RoundPairing.dualFold (n:=256) data.data.alpha0 _)) at body
  rw [weights,←funcs.1,←funcs.2] at body
  exact body

#print axioms value
end AspisR1.FJs_LiteralPair
end
