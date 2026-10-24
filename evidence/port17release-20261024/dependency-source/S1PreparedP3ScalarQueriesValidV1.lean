import S1PreparedP3ValidV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.DuplexFrames S4SolanaDigestP3RegroupV1

theorem scalar_p3_valid (B : PreparedModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) :
    OracleValid sha (PreparedScalarEffects.scalar effects B (solanaDigestP3Model copy sha) self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  apply valid_bind _ _ _ (block_p3_valid copy sha self row payload)
  intro blockResult
  repeat' first
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | apply valid_bind
    | intro x
    | split

theorem scalar_k_p3_valid (B : PreparedModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    OracleValid sha (PreparedScalarEffects.scalar_k effects B (solanaDigestP3Model copy sha) self row payload) := by
  unfold PreparedScalarEffects.scalar_k
  apply valid_bind _ _ _ (block_p3_valid copy sha self row payload)
  intro blockResult
  repeat' first
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | apply valid_bind
    | intro x
    | split

/-- This derives the structural law for all sixteen materialized calls. The
scanner and embedding may reject, but cannot supply an unproved hash law. -/
theorem queries_p3_valid (Q : QueriesModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    OracleValid sha (PreparedQueryEffects.queries effects Q (solanaDigestP3Model copy sha) self row payload) := by
  unfold PreparedQueryEffects.queries
  apply valid_bind _ _ _ (absorb_p3_valid copy sha self row payload)
  intro absorbed
  repeat' first
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | (apply valid_digest; rfl)
    | apply valid_bind
    | intro x
    | split

#print axioms scalar_p3_valid
#print axioms scalar_k_p3_valid
#print axioms queries_p3_valid
end AspisR1PublicPreparation.PreparedHashCode
