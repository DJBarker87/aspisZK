import RPu_FIr_TranscriptRange
import RPv_FJs_PreparedPoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_CircleRange
open FIr_SampleRange
open R0P.SemSource
abbrev E := OraclePortCheckpointAbiC5.E
abbrev K := OraclePortCheckpointAbiC5.K
attribute [local irreducible] QuadraticAlgebra.instInv

theorem embedded (z : AspisR0.ChordGeometry.Point K) :
    InBase (embedCirclePoint z).val.1 ∧ InBase (embedCirclePoint z).val.2 := by
  exact ⟨rfl,rfl⟩

theorem sampler0 (t : K) :
    InBase (circleSampleParameter0 t).val.1 ∧ InBase (circleSampleParameter0 t).val.2 := by
  unfold circleSampleParameter0 circleSampleParameterWith
  split
  · exact embedded _
  · exact embedded _

theorem sampler1 (t : K) :
    InBase (circleSampleParameter1 t).val.1 ∧ InBase (circleSampleParameter1 t).val.2 := by
  unfold circleSampleParameter1 circleSampleParameterWith
  split
  · exact embedded _
  · exact embedded _

theorem view (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View) (read : LiteralOpeningView.read rs=some v) (j : Fin 2) :
    InBase (v.circlePoints j).val.1 ∧ InBase (v.circlePoints j).val.2 := by
  have points := (F3M_OpeningReader.components rs v read).2.2.2
  by_cases hj : j.val=0
  · simpa only [points,if_pos hj] using sampler0 (SelectedChallengeMap.rhoOf v.challenge25)
  · simpa only [points,if_neg hj] using sampler1 (SelectedChallengeMap.rhoOf v.challenge26)

#print axioms embedded
#print axioms sampler0
#print axioms sampler1
#print axioms view
end AspisR1.FJs_CircleRange
end
