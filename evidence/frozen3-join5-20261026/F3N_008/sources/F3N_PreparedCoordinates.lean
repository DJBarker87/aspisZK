import F3N_CircleCoordinates
import F3L_SourcePrepared
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
  have x0 := congrArg Prod.fst first
  have y0 := congrArg Prod.snd first
  have x1 := congrArg Prod.fst second
  have y1 := congrArg Prod.snd second
  have pull (q : aspis_core.field.QM31) :
      SelectedChallengeMap.rhoOf (LiteralOpeningView.eK (F3L_RhoMeaning.decode q))=F3L_RhoMeaning.decode q := by rfl
  funext j
  fin_cases j <;>
    simp only [F3L_SourcePrepared.numeric,F3L_SourcePrepared.coordinate,F3L_SourcePrepared.point,
      points,Array.make,List.getElem_cons_zero,List.getElem_cons_succ,
      OraclePortAcceptedContextC6.coordinates,shape,challenge0,challenge1,
      show (0 : Nat)≠1 by decide,show (1 : Nat)≠0 by decide,
      show (2 : Nat)≠0 by decide,show (2 : Nat)≠1 by decide,
      show (3 : Nat)≠0 by decide,show (3 : Nat)≠1 by decide,show (3 : Nat)≠2 by decide,
      if_true,if_false] <;>
    first | exact (congrArg SelectedChallengeMap.rhoOf x0).symm ▸ pull point0.x
          | exact (congrArg SelectedChallengeMap.rhoOf y0).symm ▸ pull point0.y
          | exact (congrArg SelectedChallengeMap.rhoOf x1).symm ▸ pull point1.x
          | exact (congrArg SelectedChallengeMap.rhoOf y1).symm ▸ pull point1.y

#print axioms coordinates
end AspisR1.F3N_PreparedCoordinates
end
