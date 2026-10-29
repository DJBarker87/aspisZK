import R1Z.PV_RunJoin_SemanticSourceSuccess51
import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticCanonicalPost51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitSubfieldOps47 PV_RunJoin_ResultPost41

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t : host_wire.SemanticTranscript H)
    (row : U8) (framed : Slice U8) :
    Post (fun pair => match pair.1 with
      | core.result.Result.Err _ => True
      | core.result.Result.Ok q => Canonical (PV_RunJoin_SemanticScalar50.raw q))
      (@host_wire.SemanticTranscript.semantic (types base) (selected base heap box ops) H D t row framed) := by
  cases run : @host_wire.SemanticTranscript.semantic (types base) (selected base heap box ops) H D t row framed with
  | fail e => trivial
  | div => trivial
  | ok pair =>
    rcases pair with ⟨status,next⟩
    cases status with
    | Err e => trivial
    | Ok q =>
      obtain ⟨b,hb,hs,hc,hm⟩ := PV_RunJoin_SemanticSourceSuccess51.complete base heap box ops D t next row framed q run
      exact hc
#print axioms complete
end R1Z.PV_RunJoin_SemanticCanonicalPost51
