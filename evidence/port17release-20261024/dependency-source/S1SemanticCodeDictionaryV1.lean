import S1SemanticCodeVerifyExactV1
import S1PreparedOracleProgramLawsV1
import S1SemanticGhostDictionaryV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode

theorem sampleBlock_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    oracleProgram (sampleBlock first self row framed)=oracleProgram (sampleBlock second self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem semanticValidated_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    oracleProgram (semanticValidated first self record1)=oracleProgram (semanticValidated second self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem begin13_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    oracleProgram (begin13 first prefix1 transcript13 val val1 val2 val12 index_mut_back9)=oracleProgram (begin13 second prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem begin9_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    oracleProgram (begin9 first prefix1 transcript9 val val1 val2 val8 index_mut_back5)=oracleProgram (begin9 second prefix1 transcript9 val val1 val2 val8 index_mut_back5) := by
  unfold begin9
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin13_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem begin5_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    oracleProgram (begin5 first prefix1 transcript5 val val1 val2 val4 index_mut_back1)=oracleProgram (begin5 second prefix1 transcript5 val val1 val2 val4 index_mut_back1) := by
  unfold begin5
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin9_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem begin_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    oracleProgram (begin first prefix1 transcript)=oracleProgram (begin second prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin5_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem newTranscript_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    oracleProgram (newTranscript first hash publicBytes root)=oracleProgram (newTranscript second hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem publicTranscript_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    oracleProgram (publicTranscript first pub hash root)=oracleProgram (publicTranscript second pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | with_reducible apply newTranscript_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem roundStep_dictionary_irrelevant (B : RoundModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    oracleProgram (roundStep B first prefix1 transcript alpha running round)=oracleProgram (roundStep B second prefix1 transcript alpha running round) := by
  unfold roundStep
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem rounds_dictionary_irrelevant (B : RoundModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    oracleProgram (rounds B first prefix1 transcript)=oracleProgram (rounds B second prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | with_reducible apply roundStep_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem circleValidated_dictionary_irrelevant (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    oracleProgram (circleValidated B first self record1)=oracleProgram (circleValidated B second self record1) := by
  unfold circleValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem finish_dictionary_irrelevant (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) :
    oracleProgram (finish R B first pub prefix1 transcript challenges obs)=oracleProgram (finish R B second pub prefix1 transcript challenges obs) := by
  unfold finish
  repeat' first
    | (solve | with_reducible apply rounds_dictionary_irrelevant)
    | (solve | with_reducible apply circleValidated_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

theorem verify_dictionary_irrelevant (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    oracleProgram (verify (finish R B) first pub bytes hash obs)=oracleProgram (verify (finish R B) second pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | with_reducible apply publicTranscript_dictionary_irrelevant)
    | (solve | with_reducible apply begin_dictionary_irrelevant)
    | (solve | with_reducible apply finish_dictionary_irrelevant)
    | (solve | simp only [S1SemanticGhost.new_error first second, S1SemanticGhost.public_error first second, S1SemanticGhost.finish_error first second, S1SemanticGhost.finish5 first second, S1SemanticGhost.finish9 first second, S1SemanticGhost.state first second])
    | (solve | with_reducible rfl)
    | (solve | simp only [oracleProgram_digest])
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

#print axioms sampleBlock_dictionary_irrelevant
#print axioms semanticValidated_dictionary_irrelevant
#print axioms begin13_dictionary_irrelevant
#print axioms begin9_dictionary_irrelevant
#print axioms begin5_dictionary_irrelevant
#print axioms begin_dictionary_irrelevant
#print axioms newTranscript_dictionary_irrelevant
#print axioms publicTranscript_dictionary_irrelevant
#print axioms roundStep_dictionary_irrelevant
#print axioms rounds_dictionary_irrelevant
#print axioms circleValidated_dictionary_irrelevant
#print axioms finish_dictionary_irrelevant
#print axioms verify_dictionary_irrelevant
end AspisR1PublicPreparation.S1SemanticCode
