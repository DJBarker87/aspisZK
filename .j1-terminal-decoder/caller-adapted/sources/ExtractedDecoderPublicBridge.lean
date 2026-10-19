import ExtractedDecoderCallerBridge
import ExtractedWithdrawalCallerPublic

/-! Successful ASF8 decoding supplies actual same-public ASWP encoder success.
The separate semantic serializer success is explicit on the fixed nine-field
carrier and supplied transition. The parser conclusion concerns semantic bytes,
not the original ASF8 bytes; no caller/account/custody or Rust preservation
claim is made. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer
namespace AspisR1TerminalDecoder.PublicBridge

def toSerializer (p : CallerBridge.Public) : WithdrawalCarrier431.SerializerPublic :=
  AspisR1WithdrawalCaller.Carrier.toSerializer (CallerBridge.toCaller p)

def projectRaw (p : CallerBridge.Public) (t : Whole431.Transition) :
    PublicSourceRaw.Public :=
  AspisR1WithdrawalCaller.CallerPublic.projectRaw (CallerBridge.toCaller p) t

theorem decoder_serializer_parsePublic
    (asf8 : Slice U8)
    (c : pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)
    (p : CallerBridge.Public) (t : Whole431.Transition)
    (semantic : FieldsRefinement431.ByteVec)
    (hd : pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8 = ok (.Ok (.Withdrawal c p)))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (toSerializer p) t) = ok (.Ok semantic)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw p t) = some wire ∧
      SemanticPublicWire.parsePublic (semantic.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨pay, he⟩ := CallerBridge.decoder_success_encoder asf8 c p hd
  exact AspisR1WithdrawalCaller.CallerPublic.encoder_serializer_parsePublic
    (CallerBridge.toCaller p) pay t semantic he hs

#print axioms decoder_serializer_parsePublic
end AspisR1TerminalDecoder.PublicBridge
