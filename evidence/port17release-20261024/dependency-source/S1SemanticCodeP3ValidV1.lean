import S1SemanticCodeVerifyExactV1
import S1PreparedP3ValidV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode
open AspisV8R19.DuplexFrames S4SolanaDigestP3RegroupV1

theorem sampleBlock_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    OracleValid sha (sampleBlock (solanaDigestP3Model copy sha) self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem semanticValidated_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    OracleValid sha (semanticValidated (solanaDigestP3Model copy sha) self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem begin13_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    OracleValid sha (begin13 (solanaDigestP3Model copy sha) prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | with_reducible apply semanticValidated_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem begin9_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    OracleValid sha (begin9 (solanaDigestP3Model copy sha) prefix1 transcript9 val val1 val2 val8 index_mut_back5) := by
  unfold begin9
  repeat' first
    | (solve | with_reducible apply semanticValidated_p3_valid)
    | (solve | with_reducible apply begin13_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem begin5_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    OracleValid sha (begin5 (solanaDigestP3Model copy sha) prefix1 transcript5 val val1 val2 val4 index_mut_back1) := by
  unfold begin5
  repeat' first
    | (solve | with_reducible apply semanticValidated_p3_valid)
    | (solve | with_reducible apply begin9_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem begin_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    OracleValid sha (begin (solanaDigestP3Model copy sha) prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | with_reducible apply semanticValidated_p3_valid)
    | (solve | with_reducible apply begin5_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem newTranscript_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    OracleValid sha (newTranscript (solanaDigestP3Model copy sha) hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem publicTranscript_p3_valid  {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    OracleValid sha (publicTranscript (solanaDigestP3Model copy sha) pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | with_reducible apply newTranscript_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem roundStep_p3_valid (B : RoundModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    OracleValid sha (roundStep B (solanaDigestP3Model copy sha) prefix1 transcript alpha running round) := by
  unfold roundStep
  repeat' first
    | (solve | with_reducible apply semanticValidated_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem rounds_p3_valid (B : RoundModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    OracleValid sha (rounds B (solanaDigestP3Model copy sha) prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | with_reducible apply roundStep_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem circleValidated_p3_valid (B : FinishModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    OracleValid sha (circleValidated B (solanaDigestP3Model copy sha) self record1) := by
  unfold circleValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem finish_p3_valid (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) :
    OracleValid sha (finish R B (solanaDigestP3Model copy sha) pub prefix1 transcript challenges obs) := by
  unfold finish
  repeat' first
    | (solve | with_reducible apply rounds_p3_valid)
    | (solve | with_reducible apply circleValidated_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

theorem verify_p3_valid (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type} (copy : core.marker.Copy H)
    (sha : Bytes → Array U8 32#usize) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    OracleValid sha (verify (finish R B) (solanaDigestP3Model copy sha) pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | with_reducible apply publicTranscript_p3_valid)
    | (solve | with_reducible apply begin_p3_valid)
    | (solve | with_reducible apply finish_p3_valid)
    | (solve | with_reducible apply valid_lift)
    | (solve | with_reducible apply valid_pure)
    | (solve | apply valid_digest; rfl)
    | with_reducible apply valid_bind
    | intro x
    | split

#print axioms sampleBlock_p3_valid
#print axioms semanticValidated_p3_valid
#print axioms begin13_p3_valid
#print axioms begin9_p3_valid
#print axioms begin5_p3_valid
#print axioms begin_p3_valid
#print axioms newTranscript_p3_valid
#print axioms publicTranscript_p3_valid
#print axioms roundStep_p3_valid
#print axioms rounds_p3_valid
#print axioms circleValidated_p3_valid
#print axioms finish_p3_valid
#print axioms verify_p3_valid
end AspisR1PublicPreparation.S1SemanticCode
