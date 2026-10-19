import CuSavingsPublicDecodeTransfer
import ExtractedFirstHelperBinding

/-! Candidate 6 consumes the original actual-helper/serializer correspondence.
The theorem has the same downstream preparation and tx1 boundaries as the
reference theorem. Other optimization bridges remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsPublicDecodePreparation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.FirstHelperBinding

theorem entry_helper_parsePublic {E : Type} (invalidAccountData : E)
    (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (F : VerifyPrefix.Finish) (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : CuSavingsPublicDecodeTransfer.entry
      (CuSavingsPublicDecodeSource.actualBoundaries (FirstHelperBinding.tx1 B P F D) error)
      invalidAccountData asf8 proof k (some mark) =
      ok (.Ok out)) :
    ∃ s supplied view sem pre initial after challenges bytes wire,
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧
      supplied = PreparationBinding.preparationPublic s ∧
      B.view proof = ok (.Ok view) ∧
      PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      r1_semantic.public_transcript D supplied () pre.c1_root = ok (.Ok initial) ∧
      r1_wire.begin D pre initial = ok (.Ok challenges, after) ∧
      F D supplied pre after challenges
        (some (fun phase => mark (phaseToFirst phase))) = ok (.Ok sem) ∧
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1TerminalDecoder.PublicBinding.toSerializer s) = ok (.Ok bytes) ∧
      AspisR1.PublicSourceRaw.toWire (AspisR1TerminalDecoder.PublicBinding.projectRaw s) = some wire ∧
      AspisR1.SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte) =
        some (AspisR1.SemanticPublicWire.toPublic wire) ∧
      r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref bytes) pre.c1_root =
        ok (.Ok initial) := by
  rw [CuSavingsPublicDecodeTransfer.entry_eq_original_first] at h
  exact FirstHelperBinding.first_helper_parsePublic invalidAccountData B P F D
    mark error asf8 proof k out h

#print axioms entry_helper_parsePublic
end AspisR1.CuSavingsPublicDecodePreparation
