import RPz7_GExp_PreparedQueriesAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects PreparedHashEffects.new PreparedHashEffects.absorb PreparedHashEffects.block PreparedScalarEffects.scalar PreparedScalarEffects.scalar_k PreparedQueryEffects.queries

theorem preparation_associated (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply new_associated; exact law)
    | (association_then_for PreparedHashEffects.new
       <;> first | (solve | apply new_associated; exact law) | intro x)
    | (solve | apply scalar_associated; exact law)
    | (association_then_for PreparedScalarEffects.scalar
       <;> first | (solve | apply scalar_associated; exact law) | intro x)
    | (solve | apply scalar_k_associated; exact law)
    | (association_then_for PreparedScalarEffects.scalar_k
       <;> first | (solve | apply scalar_k_associated; exact law) | intro x)
    | (solve | apply queries_associated; exact law)
    | (association_then_for PreparedQueryEffects.queries
       <;> first | (solve | apply queries_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms preparation_associated
end AspisR1PublicPreparation.PreparedBudget
