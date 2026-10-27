import F3N_CircleProjection
import F3N_CoordinateShape
import F3N_ContextCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_PreparedCoordinates
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] R0P.SemSource.circleSampleParameter0 R0P.SemSource.circleSampleParameter1
  F3M_CircleSource.source F3L_RhoMeaning.decode

theorem coordinates (out : verifier.Prepared) (point0 point1 : aspis_core.circle.SecureCirclePoint)
    (block0 block1 : Array U8 32#usize)
    (points : out.z=Array.make 2#usize [point0,point1])
    (circle0 : F3M_CircleSource.source block0 .First=ok point0)
    (circle1 : F3M_CircleSource.source block1 .Second=ok point1)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View) (read : LiteralOpeningView.read rs=some v)
    (challenge0 : v.challenge25=SelectedTranscriptParams.params.σ 25 (decodeState block0))
    (challenge1 : v.challenge26=SelectedTranscriptParams.params.σ 26 (decodeState block1)) :
    (F3L_SourcePrepared.numeric out).coordinates=OraclePortAcceptedContextC6.coordinates v := by
  have shape := (F3M_OpeningReader.components rs v read).2.2.2
  have first := F3N_CircleCoordinates.first block0 point0 circle0
  have second := F3N_CircleCoordinates.second block1 point1 circle1
  have firstPair := F3N_CircleProjection.pair point0 _ first
  have secondPair := F3N_CircleProjection.pair point1 _ second
  have contextShape := F3N_ContextCoordinates.context v
    (R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf v.challenge25))
    (R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf v.challenge26)) shape
  rw [challenge0,challenge1] at contextShape
  rw [contextShape,F3N_CoordinateShape.coordinates out point0 point1 points]
  change F3N_ContextCoordinates.four _ _ _ _=F3N_ContextCoordinates.four _ _ _ _
  rw [firstPair.1,firstPair.2,secondPair.1,secondPair.2]

#print axioms coordinates
end AspisR1.F3N_PreparedCoordinates
end
