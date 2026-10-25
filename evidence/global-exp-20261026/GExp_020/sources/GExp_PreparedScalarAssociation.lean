import GExp_PreparedBlockAssociation
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedBudget
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisR1.GExp_Association
attribute [local irreducible] PreparedHashCode.effects PreparedHashEffects.new PreparedHashEffects.absorb PreparedHashEffects.block

theorem scalar_associated (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) (hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) :
    AspisR1.SdkD_PrepareLower.Associated hashv (PreparedScalarEffects.scalar effects B D self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  repeat' first
    | (solve | apply pure_associated)
    | (solve | apply lift_associated)
    | (solve | apply block_associated; exact law)
    | (association_then_for PreparedHashEffects.block
       <;> first | (solve | apply block_associated; exact law) | intro x)
    | (apply lift_bind_associated; intro x)
    | (association_then
       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)
    | split

#print axioms scalar_associated
end AspisR1PublicPreparation.PreparedBudget
