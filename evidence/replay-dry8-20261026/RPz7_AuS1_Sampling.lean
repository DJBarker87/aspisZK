import RPz7_AuS1_Hash
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Sampling
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Association AuS1_Hash

theorem scalar_uniform (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
    Uniform hashv (PreparedScalarEffects.scalar effects B D self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  repeat' first
    | (solve | apply block_uniform; assumption)
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | apply bind_uniform
    | intro x
    | split

theorem rho_uniform (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Uniform hashv (PreparedScalarEffects.scalar_k effects B D self row payload) := by
  unfold PreparedScalarEffects.scalar_k
  repeat' first
    | (solve | apply block_uniform; assumption)
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | apply bind_uniform
    | intro x
    | split

theorem queries_uniform (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Uniform hashv (PreparedQueryEffects.queries effects B D self row payload) := by
  unfold PreparedQueryEffects.queries
  repeat' first
    | (solve | apply absorb_uniform; assumption)
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | (solve | apply digest_uniform; apply law)
    | apply bind_uniform
    | intro x
    | split

#print axioms scalar_uniform
#print axioms rho_uniform
#print axioms queries_uniform
end AspisR1.AuS1_Sampling
end
