import S1PrepareBudgetTacticV1
import S1SemanticCodeSampleBlockV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result PreparedHashCode PreparedBudget
example {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    bounded 3 (sampleBlock D self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1
       · omega
       · solve | exact digest_bound _ _ _
       · intro x)
    | split

end AspisR1PublicPreparation.S1SemanticCode
