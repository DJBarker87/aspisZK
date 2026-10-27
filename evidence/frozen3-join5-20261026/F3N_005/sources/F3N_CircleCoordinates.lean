import F3M_CircleParameters
import F3M_OpeningReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_CircleCoordinates
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] R0P.SemSource.circleSample0 R0P.SemSource.circleSample1
  R0P.SemSource.circleSampleParameter0 R0P.SemSource.circleSampleParameter1
  F3M_CircleSource.source LiteralOpeningView.eK

theorem first (block : Array U8 32#usize) (p : aspis_core.circle.SecureCirclePoint)
    (success : F3M_CircleSource.source block .First=ok p) :
    F3M_CircleMeaning.coordinates p=
      (R0P.SemSource.circleSampleParameter0
        (SelectedChallengeMap.rhoOf (SelectedTranscriptParams.params.σ 25 (decodeState block)))).1 := by
  have source := F3M_CircleMeaning.returned block .First p success
  rw [F3M_CircleFirstModel.first,F3M_CircleParameters.first] at source
  exact source

theorem second (block : Array U8 32#usize) (p : aspis_core.circle.SecureCirclePoint)
    (success : F3M_CircleSource.source block .Second=ok p) :
    F3M_CircleMeaning.coordinates p=
      (R0P.SemSource.circleSampleParameter1
        (SelectedChallengeMap.rhoOf (SelectedTranscriptParams.params.σ 26 (decodeState block)))).1 := by
  have source := F3M_CircleMeaning.returned block .Second p success
  rw [F3M_CircleSecondModel.second,F3M_CircleParameters.second] at source
  exact source

#print axioms first
#print axioms second
end AspisR1.F3N_CircleCoordinates
end
