import ExtractedTerminalCallerBridge
import ExtractedWithdrawalCallerPublic

/-! Actual terminal withdrawal validation and semantic serialization imply the
live public parser equation on a fixed all-field projection. The semantic
serializer success is explicit and concerns the same public; an independently
supplied public still requires its stated equality. This does not assert runtime
reachability, account binding, or that omitted metadata is serialized. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer
namespace AspisR1TerminalValidator.PublicBridge

/-- Two previously checked fieldwise maps, fixed before observing either output. -/
def toSerializer (p : CallerBridge.Public) : WithdrawalCarrier431.SerializerPublic :=
  AspisR1WithdrawalCaller.Carrier.toSerializer (CallerBridge.toCaller p)

def projectRaw (p : CallerBridge.Public) (t : Whole431.Transition) :
    PublicSourceRaw.Public :=
  AspisR1WithdrawalCaller.CallerPublic.projectRaw (CallerBridge.toCaller p) t

theorem terminal_serializer_parsePublic
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (p : CallerBridge.Public) (t : Whole431.Transition)
    (out : FieldsRefinement431.ByteVec)
    (ht : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (.Withdrawal c p) = ok (.Ok ()))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (toSerializer p) t) = ok (.Ok out)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw p t) = some wire ∧
      SemanticPublicWire.parsePublic (out.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨aswp, he⟩ := CallerBridge.terminal_success_encoder c p ht
  exact AspisR1WithdrawalCaller.CallerPublic.encoder_serializer_parsePublic
    (CallerBridge.toCaller p) aswp t out he hs

theorem terminal_serializer_supplied_public
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (p : CallerBridge.Public) (t : Whole431.Transition)
    (out : FieldsRefinement431.ByteVec)
    (ht : pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (.Withdrawal c p) = ok (.Ok ()))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (toSerializer p) t) = ok (.Ok out))
    (wire : SemanticPublicWire.Wire)
    (hw : PublicSourceRaw.toWire (projectRaw p t) = some wire)
    (supplied : R0P.Public SemanticPublicWire.M31)
    (hbind : supplied = SemanticPublicWire.toPublic wire) :
    SemanticPublicWire.parsePublic (out.val.map RawBridge431.rawByte) = some supplied := by
  obtain ⟨aswp, he⟩ := CallerBridge.terminal_success_encoder c p ht
  exact AspisR1WithdrawalCaller.CallerPublic.encoder_serializer_supplied_public
    (CallerBridge.toCaller p) aswp t out he hs wire hw supplied hbind

#print axioms terminal_serializer_parsePublic
#print axioms terminal_serializer_supplied_public
end AspisR1TerminalValidator.PublicBridge
