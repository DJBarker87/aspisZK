import RawSamplerSuffixSourceBridge

/-! Canonical byte messages and state-threaded opening traces. This composes
local block transport without assuming a separate prefix-state equality at
every row. Reaching this trace from the verifier remains a distinct join. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.R4Transport2OpeningChain
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open TranscriptStep SourceDigestAddresses

def framed (payload : Slice U8) : Bytes :=
  PublicInitFrame.lengthBytes (UScalar.cast .U32 (Slice.len payload)).val ++ rawBytes payload

def message (payload : Slice U8) (h : (framed payload).length ≤ SelectedTranscriptParams.D) :
    SelectedTranscriptParams.Message := ⟨framed payload,h⟩

structure Call {Hash : Type} (D : aspis_core.Digest32 Hash) where
  before : transcript.Transcript Hash
  after : transcript.Transcript Hash
  row : U8
  allowed : row = 27#u8 ∨ row = 28#u8 ∨ row = 29#u8 ∨ row = 30#u8 ∨ row = 32#u8
  payload : Slice U8
  block : Bytes32
  source : transcript.Transcript.block D before row payload = ok (block,after)
  fits : (framed payload).length ≤ SelectedTranscriptParams.D
  literal : LiteralTranscript.Message
  erased : LiteralTranscript.erase literal = .payload (message payload fits)

def sourceValue {Hash : Type} {D : aspis_core.Digest32 Hash} (c : Call D) :
    LiteralTranscript.Challenge :=
  (.ordinary (SelectedChallengeMap.sigma c.row.val (decodeState c.block)),decodeState c.after.state)

theorem call_transport {Hash : Type} (D : aspis_core.Digest32 Hash) (c : Call D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState c.before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
      (LiteralTranscript.samp c.row.val P c.literal).toProgram).2 = sourceValue c := by
  have hr : c.row.val < 33 := by
    rcases c.allowed with h|h|h|h|h <;> rw [h] <;> decide
  have hbound : (160#u8).val + c.row.val ≤ U8.max := by scalar_tac
  obtain ⟨tag, htag, hval⟩ := WP.spec_imp_exists
    (U8.add_spec (x := 160#u8) (y := c.row) hbound)
  have hlabel : SelectedTranscriptParams.params.lbl c.row.val = decodeByte tag := by
    apply Fin.ext
    change (SelectedTranscriptParams.label c.row.val).val = tag.val
    rw [SelectedTranscriptParams.label_val _ hr]
    simpa using hval.symm
  have hi : c.row.val = 27 ∨ c.row.val = 28 ∨ c.row.val = 29 ∨
      c.row.val = 30 ∨ c.row.val = 32 := by
    rcases c.allowed with h|h|h|h|h <;> rw [h] <;> decide
  exact SamplerSuffixSourceBridge.opening_block_correspondence D c.before c.after c.row tag
    c.payload (UScalar.cast .U32 (Slice.len c.payload)) c.block c.source htag rfl
    P c.row.val hi hlabel c.literal (message c.payload c.fits) c.erased hstate rfl H hdigest

inductive Trace {Hash : Type} (D : aspis_core.Digest32 Hash) :
    transcript.Transcript Hash → transcript.Transcript Hash → List (Call D) → Prop
  | nil (s) : Trace D s s []
  | cons (c : Call D) {last cs} (tail : Trace D c.after last cs) : Trace D c.before last (c::cs)

def sourcePrefix {Hash : Type} {D : aspis_core.Digest32 Hash} :
    LiteralTranscript.Prefix → List (Call D) → LiteralTranscript.Prefix
  | P, [] => P
  | P, c::cs => sourcePrefix (P.ext c.literal (sourceValue c)) cs

def modelPrefix {Hash : Type} {D : aspis_core.Digest32 Hash} (H : Bytes → State) :
    LiteralTranscript.Prefix → List (Call D) → LiteralTranscript.Prefix
  | P, [] => P
  | P, c::cs => modelPrefix H (P.ext c.literal
      (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
        (LiteralTranscript.samp c.row.val P c.literal).toProgram).2) cs

/-- One initial checkpoint-state equality threads through every reached block.
Payload lengths/labels are constructed from source data, not repeated hypotheses. -/
theorem trace_transport {Hash : Type} (D : aspis_core.Digest32 Hash)
    {before after : transcript.Transcript Hash} {cs : List (Call D)}
    (run : Trace D before after cs) (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState before.state)
    (H : Bytes → State)
    (hdigest : ∀ hash parts out, D.digest hash parts = ok out →
      decodeState out = H (flatten parts)) :
    modelPrefix H P cs = sourcePrefix P cs ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (sourcePrefix P cs)) = decodeState after.state := by
  induction run generalizing P with
  | nil s => exact ⟨rfl,hstate⟩
  | cons c tail ih =>
    have hcall := call_transport D c P hstate H hdigest
    have hn : UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (P.ext c.literal (sourceValue c))) =
        decodeState c.after.state := by
      rw [LiteralTranscript.erasePrefix_ext, UnifiedSampler.stateOf_ext]
      rfl
    have ht := ih (P.ext c.literal (sourceValue c)) hn
    simpa only [modelPrefix, sourcePrefix, hcall] using ht

#print axioms call_transport
#print axioms trace_transport
end AspisR1PublicPreparation.R4Transport2OpeningChain
end
