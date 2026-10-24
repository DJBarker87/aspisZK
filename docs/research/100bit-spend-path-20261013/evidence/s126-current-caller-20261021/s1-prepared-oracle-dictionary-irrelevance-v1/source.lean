import S1PreparedOracleProgramLawsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

theorem new_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (hash : H) (state : Array U8 32#usize) (variant : transport.Variant) :
    oracleProgram (PreparedHashEffects.new effects first hash state variant)=
      oracleProgram (PreparedHashEffects.new effects second hash state variant) := by
  unfold PreparedHashEffects.new
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem absorb_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    oracleProgram (PreparedHashEffects.absorb effects first self row payload)=
      oracleProgram (PreparedHashEffects.absorb effects second self row payload) := by
  unfold PreparedHashEffects.absorb
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem block_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    oracleProgram (PreparedHashEffects.block effects first self row payload)=
      oracleProgram (PreparedHashEffects.block effects second self row payload) := by
  unfold PreparedHashEffects.block
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | with_reducible apply absorb_oracle_dictionary_irrelevant)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

#print axioms new_oracle_dictionary_irrelevant
#print axioms absorb_oracle_dictionary_irrelevant
#print axioms block_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode
