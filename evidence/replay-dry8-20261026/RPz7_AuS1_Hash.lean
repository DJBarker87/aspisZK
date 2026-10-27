import RPz7_AuS1_Association
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Hash
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Association
theorem new_uniform {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (hash : H)
    (state : Array U8 32#usize) (variant : transport.Variant) :
    Uniform hashv (PreparedHashEffects.new effects D hash state variant) := by
  unfold PreparedHashEffects.new
  repeat' first
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | (apply digest_uniform; apply law)
    | apply bind_uniform
    | intro x
    | split

theorem absorb_uniform {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    Uniform hashv (PreparedHashEffects.absorb effects D self row payload) := by
  unfold PreparedHashEffects.absorb
  repeat' first
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | (apply digest_uniform; apply law)
    | apply bind_uniform
    | intro x
    | split

theorem block_uniform {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    Uniform hashv (PreparedHashEffects.block effects D self row payload) := by
  unfold PreparedHashEffects.block
  repeat' first
    | (solve | apply absorb_uniform; assumption)
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | (apply digest_uniform; apply law)
    | apply bind_uniform
    | intro x
    | split


#print axioms new_uniform
#print axioms absorb_uniform
#print axioms block_uniform
end AspisR1.AuS1_Hash
end
