import NJG_RoundsCode
set_option autoImplicit false
namespace AspisR1.NJG_RoundsUnrolled
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (Code run)
attribute [local irreducible] S1SemanticCode.roundStep

/-- Symbolic one-site join; no reduction of roundStep, field arithmetic or hash. -/
theorem one {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (r : Usize) (rest : List Usize) (carry : Carry H) :
 chain B D pre (r::rest) carry=(do
  let reply←S1SemanticCode.roundStep B D pre carry.2.2 carry.2.1 carry.1 r
  let cf←core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | .Continue next=>chain B D pre rest next
  | .Break residual=>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (Carry H) (core.convert.FromSame r1_wire.Error) residual) := rfl

/-- Callee-opaque finite join, replacing L060's broad kernel normalization.
Every original call, error arm and SAME carry remains literally present. -/
theorem source {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 NJG_RoundsCode.source B D pre t=S1SemanticCode.rounds B D pre t := by
 unfold NJG_RoundsCode.source S1SemanticCode.rounds
 rfl

theorem ordered {H : Type} (B : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) :
 run (NJG_RoundsCode.source B D pre t)=run (S1SemanticCode.rounds B D pre t) := congrArg run (source B D pre t)

#print axioms one
#print axioms source
#print axioms ordered
end AspisR1.NJG_RoundsUnrolled
