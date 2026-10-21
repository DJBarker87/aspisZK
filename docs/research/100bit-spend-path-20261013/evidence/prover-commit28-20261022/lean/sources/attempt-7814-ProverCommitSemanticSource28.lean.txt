import R1Z.ProverCommitSemanticProgram28
import R1Z.ProverCommitCircleProgram28
/-! Pure specialization reconstructs both retained callers verbatim. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSemanticSource28
open Aeneas Aeneas.Std Result

theorem sample {H : Type} (hash : AspisR1SimSemantic20.aspis_core.digest.Digest32 H)
    (s : AspisR1SimSemantic20.r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    AspisR1SimSemantic20.r1_wire.SemanticTranscript.sample_block_validated hash s row framed =
    ProverCommitSemanticProgram28.sample hash.digest s row framed := by rfl

theorem semantic {H : Type} (hash : AspisR1SimSemantic20.aspis_core.digest.Digest32 H)
    (s : AspisR1SimSemantic20.r1_wire.SemanticTranscript H) (row : U8)
    (record : alloc.vec.Vec U8) :
    AspisR1SimSemantic20.r1_wire.semantic20.semantic hash s row record =
    ProverCommitSemanticProgram28.semantic hash.digest s row record := by rfl

theorem circle_sample {H : Type} (hash : AspisR1CircleCaller25.aspis_core.digest.Digest32 H)
    (s : AspisR1CircleCaller25.r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    AspisR1CircleCaller25.r1_wire.SemanticTranscript.sample_block_validated hash s row framed =
    ProverCommitCircleProgram28.sample hash.digest s row framed := by rfl

theorem circle {H P : Type} (hash : AspisR1CircleCaller25.aspis_core.digest.Digest32 H)
    (policy : AspisR1CircleCaller25.r1_wire.circle25.Policy P)
    (s : AspisR1CircleCaller25.r1_wire.SemanticTranscript H) (row : U8)
    (record : alloc.vec.Vec U8) :
    AspisR1CircleCaller25.r1_wire.circle25.point hash policy s row record =
    ProverCommitCircleProgram28.point hash.digest policy s row record := by rfl

#print axioms sample
#print axioms semantic
#print axioms circle_sample
#print axioms circle
end R1Z.ProverCommitSemanticSource28
