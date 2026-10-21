import R4Transport2OpeningChain

/-! The first-25 checkpoint can feed both circle calls, the S2 reseed and
any reached ordinary opening trace, with one carried-state premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4Transport2CirclePrefix
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

def semanticMessage (payload : Slice U8)
    (h : (rawBytes payload).length ≤ SelectedTranscriptParams.D) : LiteralTranscript.Message :=
  .payload ⟨rawBytes payload,h⟩

def extendModel (H : Bytes → State) (i : Nat) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) : LiteralTranscript.Prefix :=
  P.ext m (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
    (LiteralTranscript.samp i P m).toProgram).2

theorem circle25_state {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D before 25#u8 payload =
      ok (.Ok block,after))
    (hfits : (rawBytes payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (extendModel H 25 P (semanticMessage payload hfits))) =
      decodeState after.state := by
  have h := SamplerSuffixSourceBridge.circle25_correspondence D before after payload block hcall
    P (semanticMessage payload hfits) ⟨rawBytes payload,hfits⟩ rfl hstate rfl H hdigest
  rw [extendModel, LiteralTranscript.erasePrefix_ext, UnifiedSampler.stateOf_ext, h]

theorem circle26_reseed_state {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : r1_wire.SemanticTranscript Hash) (payload : Slice U8) (block : Bytes32)
    (hcall : r1_wire.SemanticTranscript.sample_block_validated D before 26#u8 payload =
      ok (.Ok block,after))
    (hash : Hash) (opening : transcript.Transcript Hash)
    (hnew : transcript.Transcript.new D hash after.state .S2 = ok opening)
    (hfits : (rawBytes payload).length ≤ SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (htag : P.statement.tag = (2 : AspisV8R19.DuplexFrames.Byte))
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (extendModel H 26 P (semanticMessage payload hfits))) =
      decodeState opening.state := by
  have ht : P.statement.tag = decodeByte (CallerStep.variantTag .S2) := by
    rw [SamplerSuffixSourceFrames.s2_tag]
    exact htag
  have h := SamplerSuffixSourceBridge.circle26_correspondence D before after payload block hcall
    hash .S2 opening hnew P (semanticMessage payload hfits) ⟨rawBytes payload,hfits⟩
    rfl hstate rfl ht H hdigest
  rw [extendModel, LiteralTranscript.erasePrefix_ext, UnifiedSampler.stateOf_ext, h]

/-- Source successes and one first-25 checkpoint equality compose. No later
state equality or byte-encoding equality is assumed separately. The trace's
caller reachability and literal constructor binding are explicit data. -/
theorem circles_then_opening {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before mid after : r1_wire.SemanticTranscript Hash)
    (payload25 payload26 : Slice U8) (block25 block26 : Bytes32)
    (hc25 : r1_wire.SemanticTranscript.sample_block_validated D before 25#u8 payload25 =
      ok (.Ok block25,mid))
    (hc26 : r1_wire.SemanticTranscript.sample_block_validated D mid 26#u8 payload26 =
      ok (.Ok block26,after))
    (hash : Hash) (opening last : transcript.Transcript Hash)
    (hnew : transcript.Transcript.new D hash after.state .S2 = ok opening)
    (fits25 : (rawBytes payload25).length ≤ SelectedTranscriptParams.D)
    (fits26 : (rawBytes payload26).length ≤ SelectedTranscriptParams.D)
    (cs : List (R4Transport2OpeningChain.Call D))
    (run : R4Transport2OpeningChain.Trace D opening last cs)
    (P : LiteralTranscript.Prefix) (htag : P.statement.tag = (2 : AspisV8R19.DuplexFrames.Byte))
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    let P26 := extendModel H 25 P (semanticMessage payload25 fits25)
    let P27 := extendModel H 26 P26 (semanticMessage payload26 fits26)
    R4Transport2OpeningChain.modelPrefix H P27 cs =
      R4Transport2OpeningChain.sourcePrefix P27 cs ∧
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (R4Transport2OpeningChain.sourcePrefix P27 cs)) =
      decodeState last.state := by
  let P26 := extendModel H 25 P (semanticMessage payload25 fits25)
  have hs26 := circle25_state D before mid payload25 block25 hc25 fits25 P hstate H hdigest
  have ht26 : P26.statement.tag = (2 : AspisV8R19.DuplexFrames.Byte) := htag
  have hs27 := circle26_reseed_state D mid after payload26 block26 hc26 hash opening hnew
    fits26 P26 ht26 hs26 H hdigest
  exact R4Transport2OpeningChain.trace_transport D run _ hs27 H hdigest

#print axioms circle25_state
#print axioms circle26_reseed_state
#print axioms circles_then_opening
end AspisR1PublicPreparation.R4Transport2CirclePrefix
end
