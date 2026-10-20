import RawTx1DigestLog
import RawSamplerSuffixSourceBridge

/-! Apply the landed suffix bridges to the SAME byte-oracle premise as tx1.
No full row-31 source trace or suffix inventory completeness is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.Tx1SamplerSuffixOracle
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1 AspisR1.RawSamplerSuffixCorrespondence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses Tx1DigestLog

theorem backend_interpretation {Hash : Type} {D : aspis_core.Digest32 Hash}
    (H : Bytes → State) (hbackend : ByteOracleBackend D H)
    (hash : Hash) (parts : Slice (Slice U8)) (out : Bytes32)
    (hcall : D.digest hash parts = ok out) :
    decodeState out = H (flatten parts) :=
  hbackend _ ⟨hash, parts, out, rfl, hcall⟩

theorem opening_block_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : transcript.Transcript Hash) (row tag : U8)
    (payload : Slice U8) (n : U32) (block : Bytes32)
    (hcall : transcript.Transcript.block D self row payload = ok (block, after))
    (htag : 160#u8 + row = ok tag)
    (hlen : UScalar.cast .U32 (Slice.len payload) = n)
    (P : LiteralTranscript.Prefix) (i : Nat)
    (hi : i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 32)
    (hlabel : SelectedTranscriptParams.params.lbl i = decodeByte tag)
    (m : LiteralTranscript.Message) (b : SelectedTranscriptParams.Message)
    (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b =
      AspisR1.PublicInitFrame.lengthBytes n.val ++ rawBytes payload)
    (H : Bytes → State)
    (hbackend : ByteOracleBackend D H) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp i P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma i (decodeState block)),
        decodeState after.state) := by
  exact SamplerSuffixSourceBridge.opening_block_correspondence D self after row tag payload n block hcall htag hlen P i hi hlabel m b hm hstate hbytes H
    (backend_interpretation H hbackend)

theorem circle25_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D self 25#u8 payload =
      ok (.Ok block, after))
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (b : SelectedTranscriptParams.Message) (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b = rawBytes payload)
    (H : Bytes → State)
    (hbackend : ByteOracleBackend D H) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 25 P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 25 (decodeState block)), decodeState after.state) := by
  exact SamplerSuffixSourceBridge.circle25_correspondence D self after payload block hcall P m b hm hstate hbytes H
    (backend_interpretation H hbackend)

theorem circle26_correspondence {Hash : Type} (D : aspis_core.Digest32 Hash)
    (self after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D self 26#u8 payload =
      ok (.Ok block, after))
    (hash : Hash) (variant : transport.Variant) (opening : transcript.Transcript Hash)
    (hnew : transcript.Transcript.new D hash after.state variant = ok opening)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (b : SelectedTranscriptParams.Message) (hm : LiteralTranscript.erase m = .payload b)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState self.state)
    (hbytes : SelectedTranscriptParams.params.enc b = rawBytes payload)
    (htag : P.statement.tag = decodeByte (CallerStep.variantTag variant))
    (H : Bytes → State)
    (hbackend : ByteOracleBackend D H) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp 26 P m).toProgram).2 =
      (.ordinary (SelectedChallengeMap.sigma 26 (decodeState block)), decodeState opening.state) := by
  exact SamplerSuffixSourceBridge.circle26_correspondence D self after payload block hcall hash variant opening hnew P m b hm hstate hbytes htag H
    (backend_interpretation H hbackend)

#print axioms backend_interpretation
#print axioms opening_block_correspondence
#print axioms circle25_correspondence
#print axioms circle26_correspondence
end AspisR1PublicPreparation.Tx1SamplerSuffixOracle
end
