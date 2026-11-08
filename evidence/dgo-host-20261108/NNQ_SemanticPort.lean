import NNQ_PreparedPort
noncomputable section
set_option autoImplicit false
namespace AspisR1PublicPreparation.NNQ_Ghost
open Aeneas Aeneas.Std Result

theorem new_error {H : Type} (first second : aspis_core.Digest32 H) :
    r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError first=
      r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError second := by
  unfold r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
    r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once
  rfl

theorem public_error {H : Type} (first second : aspis_core.Digest32 H) :
    r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError first=
      r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError second := by
  unfold r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

theorem finish_error {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn11 first=FinishModel.closureFn11 second := by
  unfold FinishModel.closureFn11 FinishModel.closureFn10
  rfl

theorem finish5 {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn5 first=FinishModel.closureFn5 second := by
  unfold FinishModel.closureFn5 FinishModel.closureFn4 FinishModel.closureFn3 FinishModel.closureFn2
  rfl

theorem finish9 {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn9 first=FinishModel.closureFn9 second := by
  unfold FinishModel.closureFn9 FinishModel.closureFn8 FinishModel.closureFn7 FinishModel.closureFn6
  rfl

theorem state {H : Type} (first second : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H) :
    r1_wire.SemanticTranscript.impl.state first t=r1_wire.SemanticTranscript.impl.state second t := by
  unfold r1_wire.SemanticTranscript.impl.state
  rfl

#print axioms new_error
#print axioms public_error
#print axioms finish_error
#print axioms finish5
#print axioms finish9
#print axioms state
end AspisR1PublicPreparation.NNQ_Ghost

set_option autoImplicit false
open AspisR1.NNQ_HostDigest
namespace AspisR1PublicPreparation.S1SemanticCode.NNQ_Port
open Aeneas Aeneas.Std Result
open PreparedHashCode

theorem sampleBlock_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) :
    DSim (sampleBlock first self row framed) (sampleBlock second self row framed) := by
  unfold sampleBlock
  repeat' first
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem semanticValidated_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    DSim (semanticValidated first self record1) (semanticValidated second self record1) := by
  unfold semanticValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem begin13_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript13 : r1_wire.SemanticTranscript H)
    (val val1 val2 val12 : aspis_core.field.QM31)
    (index_mut_back9 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    DSim (begin13 first prefix1 transcript13 val val1 val2 val12 index_mut_back9) (begin13 second prefix1 transcript13 val val1 val2 val12 index_mut_back9) := by
  unfold begin13
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem begin9_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript9 : r1_wire.SemanticTranscript H)
    (val val1 val2 val8 : aspis_core.field.QM31)
    (index_mut_back5 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    DSim (begin9 first prefix1 transcript9 val val1 val2 val8 index_mut_back5) (begin9 second prefix1 transcript9 val val1 val2 val8 index_mut_back5) := by
  unfold begin9
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin13_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem begin5_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript5 : r1_wire.SemanticTranscript H)
    (val val1 val2 val4 : aspis_core.field.QM31)
    (index_mut_back1 : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
    DSim (begin5 first prefix1 transcript5 val val1 val2 val4 index_mut_back1) (begin5 second prefix1 transcript5 val val1 val2 val4 index_mut_back1) := by
  unfold begin5
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin9_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem begin_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    DSim (begin first prefix1 transcript) (begin second prefix1 transcript) := by
  unfold begin
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | with_reducible apply begin5_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem newTranscript_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (hash : H) (publicBytes : Slice U8) (root : Array U8 32#usize) :
    DSim (newTranscript first hash publicBytes root) (newTranscript second hash publicBytes root) := by
  unfold newTranscript
  repeat' first
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem publicTranscript_dictionary_irrelevant  {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (root : Array U8 32#usize) :
    DSim (publicTranscript first pub hash root) (publicTranscript second pub hash root) := by
  unfold publicTranscript
  repeat' first
    | (solve | with_reducible apply newTranscript_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem roundStep_dictionary_irrelevant (B : RoundModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31) (round : Usize) :
    DSim (roundStep B first prefix1 transcript alpha running round) (roundStep B second prefix1 transcript alpha running round) := by
  unfold roundStep
  repeat' first
    | (solve | with_reducible apply semanticValidated_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem rounds_dictionary_irrelevant (B : RoundModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (prefix1 : r1_wire.Prefix) (transcript : r1_wire.SemanticTranscript H) :
    DSim (rounds B first prefix1 transcript) (rounds B second prefix1 transcript) := by
  unfold rounds
  repeat' first
    | (solve | with_reducible apply roundStep_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem circleValidated_dictionary_irrelevant (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : r1_wire.SemanticTranscript H) (record1 : r1_wire.ValidatedRecord) :
    DSim (circleValidated B first self record1) (circleValidated B second self record1) := by
  unfold circleValidated
  repeat' first
    | (solve | with_reducible apply sampleBlock_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem finish_dictionary_irrelevant (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (prefix1 : r1_wire.Prefix)
    (transcript : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) :
    DSim (finish R B first pub prefix1 transcript challenges obs) (finish R B second pub prefix1 transcript challenges obs) := by
  unfold finish
  repeat' first
    | (solve | with_reducible apply rounds_dictionary_irrelevant)
    | (solve | with_reducible apply circleValidated_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem verify_dictionary_irrelevant (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    DSim (verify (finish R B) first pub bytes hash obs) (verify (finish R B) second pub bytes hash obs) := by
  unfold verify
  repeat' first
    | (solve | with_reducible apply publicTranscript_dictionary_irrelevant)
    | (solve | with_reducible apply begin_dictionary_irrelevant)
    | (solve | with_reducible apply finish_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
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
end AspisR1PublicPreparation.S1SemanticCode.NNQ_Portend
