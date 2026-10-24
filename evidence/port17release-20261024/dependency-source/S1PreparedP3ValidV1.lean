import S1PreparedOracleCodeV1
import S1PreparedCompleteHashErasureV1
import S4SolanaDigestP3RegroupV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.DuplexFrames
open S4SolanaDigestP3RegroupV1

theorem new_p3_valid {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (hash : H)
    (state : Array U8 32#usize) (variant : transport.Variant) :
    OracleValid sha (PreparedHashEffects.new effects (solanaDigestP3Model copy sha) hash state variant) := by
  unfold PreparedHashEffects.new
  repeat' first
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | (apply valid_digest; rfl)
    | apply valid_bind
    | intro x
    | split

theorem absorb_p3_valid {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    OracleValid sha (PreparedHashEffects.absorb effects (solanaDigestP3Model copy sha) self row payload) := by
  unfold PreparedHashEffects.absorb
  repeat' first
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | (apply valid_digest; rfl)
    | apply valid_bind
    | intro x
    | split

theorem block_p3_valid {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    OracleValid sha (PreparedHashEffects.block effects (solanaDigestP3Model copy sha) self row payload) := by
  unfold PreparedHashEffects.block
  repeat' first
    | (solve | apply absorb_p3_valid)
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | (apply valid_digest; rfl)
    | apply valid_bind
    | intro x
    | split

#print axioms new_p3_valid
#print axioms absorb_p3_valid
#print axioms block_p3_valid
end AspisR1PublicPreparation.PreparedHashCode
