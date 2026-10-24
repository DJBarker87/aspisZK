import S1PrepareBudgetCoreV1
import S1SemanticCodeSampleBlockV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result PreparedHashCode PreparedBudget
attribute [local irreducible] PreparedHashCode.effects
example {H : Type} (D : aspis_core.Digest32 H)
    (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    bounded 3 (sampleBlock D self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (apply then_bound (p:=effects.digest _ _ _) (cost:=1)
       · omega
       · solve | apply digest_bound
       · intro x)
    | split
end AspisR1PublicPreparation.S1SemanticCode
