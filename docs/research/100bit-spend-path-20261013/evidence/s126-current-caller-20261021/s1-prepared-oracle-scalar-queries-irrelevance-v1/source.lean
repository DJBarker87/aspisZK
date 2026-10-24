import S1PreparedOracleDictionaryIrrelevanceV1
import S1PreparedQueryEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow

theorem scalar_oracle_dictionary_irrelevant (B : PreparedModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) :
    oracleProgram (PreparedScalarEffects.scalar effects B first self row payload nonzero)=
      oracleProgram (PreparedScalarEffects.scalar effects B second self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | with_reducible apply block_oracle_dictionary_irrelevant)
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem scalar_k_oracle_dictionary_irrelevant (B : PreparedModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    oracleProgram (PreparedScalarEffects.scalar_k effects B first self row payload)=
      oracleProgram (PreparedScalarEffects.scalar_k effects B second self row payload) := by
  unfold PreparedScalarEffects.scalar_k
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | with_reducible apply block_oracle_dictionary_irrelevant)
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem queries_oracle_dictionary_irrelevant (Q : QueriesModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    oracleProgram (PreparedQueryEffects.queries effects Q first self row payload)=
      oracleProgram (PreparedQueryEffects.queries effects Q second self row payload) := by
  unfold PreparedQueryEffects.queries
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | with_reducible apply absorb_oracle_dictionary_irrelevant)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

#print axioms scalar_oracle_dictionary_irrelevant
#print axioms scalar_k_oracle_dictionary_irrelevant
#print axioms queries_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode
