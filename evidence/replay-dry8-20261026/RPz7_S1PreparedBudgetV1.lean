import RPz7_S1PrepareBudgetTacticV1
import RPz7_S1PreparedCompleteHashErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result
open PreparedHashCode
attribute [local irreducible] PreparedHashCode.effects

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem new_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (hash : H) (state : Array U8 32#usize) (variant : transport.Variant) : bounded 1 (PreparedHashEffects.new effects D hash state variant) := by
  unfold PreparedHashEffects.new
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedHashEffects.new

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem absorb_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) : bounded 1 (PreparedHashEffects.absorb effects D self row payload) := by
  unfold PreparedHashEffects.absorb
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedHashEffects.absorb

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem block_bounded  {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) : bounded 3 (PreparedHashEffects.block effects D self row payload) := by
  unfold PreparedHashEffects.block
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1) <;> first | omega | (solve | apply absorb_bounded))
    | (budget_then_for 1 PreparedHashEffects.absorb
       <;> first | omega | (solve | apply absorb_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedHashEffects.block

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem scalar_bounded (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) : bounded 3 (PreparedScalarEffects.scalar effects B D self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3) <;> first | omega | (solve | apply block_bounded))
    | (budget_then_for 3 PreparedHashEffects.block
       <;> first | omega | (solve | apply block_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedScalarEffects.scalar

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem scalar_k_bounded (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) : bounded 3 (PreparedScalarEffects.scalar_k effects B D self row payload) := by
  unfold PreparedScalarEffects.scalar_k
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=3) <;> first | omega | (solve | apply block_bounded))
    | (budget_then_for 3 PreparedHashEffects.block
       <;> first | omega | (solve | apply block_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedScalarEffects.scalar_k

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem queries_bounded (Q : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) : bounded 17 (PreparedQueryEffects.queries effects Q D self row payload) := by
  unfold PreparedQueryEffects.queries
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1) <;> first | omega | (solve | apply absorb_bounded))
    | (budget_then_for 1 PreparedHashEffects.absorb
       <;> first | omega | (solve | apply absorb_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedQueryEffects.queries

/-- Counts every materialized digest on every response path, with rejection prefixes. -/
theorem preparation_bounded (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) : bounded 33 (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply mono (n:=1) <;> first | omega | (solve | apply new_bounded))
    | (budget_then_for 1 PreparedHashEffects.new
       <;> first | omega | (solve | apply new_bounded) | intro x)
    | (apply mono (n:=3) <;> first | omega | (solve | apply scalar_bounded))
    | (budget_then_for 3 PreparedScalarEffects.scalar
       <;> first | omega | (solve | apply scalar_bounded) | intro x)
    | (apply mono (n:=3) <;> first | omega | (solve | apply scalar_k_bounded))
    | (budget_then_for 3 PreparedScalarEffects.scalar_k
       <;> first | omega | (solve | apply scalar_k_bounded) | intro x)
    | (apply mono (n:=17) <;> first | omega | (solve | apply queries_bounded))
    | (budget_then_for 17 PreparedQueryEffects.queries
       <;> first | omega | (solve | apply queries_bounded) | intro x)
    | (apply lift_bind;intro x)
    | (budget_then 1 <;> first | omega | (solve | exact digest_bound _ _ _) | intro x)
    | split

attribute [local irreducible] PreparedSourceEffects.prepare

#print axioms new_bounded
#print axioms absorb_bounded
#print axioms block_bounded
#print axioms scalar_bounded
#print axioms scalar_k_bounded
#print axioms queries_bounded
#print axioms preparation_bounded
end AspisR1PublicPreparation.PreparedBudget
