import NNQ_SemanticPort
import PIN2_S1SemanticCodeVerifyV1
/-! PIN2 W10 (2026-11-11): NEW module, PIN2 twins of the NNQ_SemanticPort dictionary-irrelevance
lemmas for the PIN2 lifted code (W7): PIN2 `newTranscript`/`publicTranscript` (namespace
AspisR1PublicPreparationPIN2.S1SemanticCode), the frozen-carrier wrapper `publicTranscriptPIN2`
and `verifyPIN2`.  Same tactic scripts as the release module; the two PIN2 error-closure ghost
facts are the release `NNQ_Ghost.new_error`/`public_error` on the PIN2 closures.  The release
NNQ_SemanticPort is unchanged (its lemmas remain valid for the frozen code). -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PIN2_NNQ_Ghost
open Aeneas Aeneas.Std Result

theorem new_error {H : Type} (first second : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError first=
      AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError second := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once
  rfl

theorem public_error {H : Type} (first second : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) :
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError first=
      AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError second := by
  unfold AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

#print axioms new_error
#print axioms public_error
end AspisR1PublicPreparation.PIN2_NNQ_Ghost

namespace AspisR1PublicPreparation.S1SemanticCode.PIN2_NNQ_Port
open Aeneas Aeneas.Std Result AspisR1.NNQ_HostDigest
open AspisR1PublicPreparation.PreparedHashCode

theorem newTranscript_dictionary_irrelevant {H : Type}
    (first second : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H) (hash : H)
    (publicBytes : Slice U8) (root : Array U8 32#usize) :
    DSim (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript first hash publicBytes root)
      (AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript second hash publicBytes root) := by
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.newTranscript
  repeat' first
    | (solve | simp only [PIN2_NNQ_Ghost.new_error first second, PIN2_NNQ_Ghost.public_error first second]; with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_if
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem publicTranscript_dictionary_irrelevant {H : Type}
    (first second : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
    (root : Array U8 32#usize) :
    DSim (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript first pub hash root)
      (AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript second pub hash root) := by
  unfold AspisR1PublicPreparationPIN2.S1SemanticCode.publicTranscript
  repeat' first
    | (solve | with_reducible apply newTranscript_dictionary_irrelevant)
    | (solve | simp only [PIN2_NNQ_Ghost.new_error first second, PIN2_NNQ_Ghost.public_error first second]; with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_if
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem publicTranscriptPIN2_dictionary_irrelevant {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
    (root : Array U8 32#usize) :
    DSim (publicTranscriptPIN2 first pub hash root) (publicTranscriptPIN2 second pub hash root) := by
  unfold publicTranscriptPIN2
  apply dsim_bind
  · apply publicTranscript_dictionary_irrelevant
  · intro x
    exact dsim_refl _

theorem verifyPIN2_dictionary_irrelevant (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    DSim (verifyPIN2 (finish R B) first pub bytes hash obs) (verifyPIN2 (finish R B) second pub bytes hash obs) := by
  unfold verifyPIN2
  repeat' first
    | (solve | with_reducible apply publicTranscriptPIN2_dictionary_irrelevant)
    | (solve | with_reducible apply NNQ_Port.begin_dictionary_irrelevant)
    | (solve | with_reducible apply NNQ_Port.finish_dictionary_irrelevant)
    | (solve | simp only [NNQ_Ghost.new_error first second, NNQ_Ghost.public_error first second, NNQ_Ghost.finish_error first second, NNQ_Ghost.finish5 first second, NNQ_Ghost.finish9 first second, NNQ_Ghost.state first second ]; with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_if
    | with_reducible apply dsim_bind
    | intro x
    | split

#print axioms newTranscript_dictionary_irrelevant
#print axioms publicTranscript_dictionary_irrelevant
#print axioms publicTranscriptPIN2_dictionary_irrelevant
#print axioms verifyPIN2_dictionary_irrelevant
end AspisR1PublicPreparation.S1SemanticCode.PIN2_NNQ_Port
end
