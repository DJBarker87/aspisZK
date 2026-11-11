import R1LiteralByteProtocol
import RawTranscriptFrameBytes
import R1SelectedChallengeMap
import AspisRows40Labels

/-! Aspis one-transaction verifier: the 40-row sampler and byte protocol.

R1's sampler `UnifiedSampler.samp` is already total in the row number: every
payload row other than 0, 26 (reseed) and 31 (queries) is a plain duplex row
`absorb, squeeze, advance` with the row's challenge map. Rows 33 to 39 of the
Aspis transcript are exactly such rows (transcript.rs `scalar_k`, lines 36-39,
via `block`, lines 22-27, and `absorb`, lines 19-21). So the 40-row sampler IS
R1's sampler, and the only hard-wired 33 in the protocol is the field
`r := 33` of `LiteralByteProtocol.protocol`. This file defines the 40-row
protocol as a parallel definition, proves it agrees with R1's protocol in every
field but `r` and in every transcript prefix and chain, and states the exact
bytes of the new rows' frames.

The payload of each new row is 64 bytes, framed as in every R1 transcript.rs
row: the four little-endian bytes of the length (64, 0, 0, 0) followed by the
payload (`absorb`, transcript.rs line 20; R1 framing
`RawTranscriptFrameBytes.absorb` and `F3J_LengthFrame.framed`). Not a security
theorem; not a source refinement of fused.rs beyond the frame bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Protocol

open FS FS2 FS2.Duplex
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

abbrev p := SelectedTranscriptParams.params
abbrev L := SelectedTranscriptParams.L

theorem hD : 5 ≤ p.D := by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]

/-! ## Sampler -/

/-- The 40-row sampler over bounded addresses: R1's, unchanged. -/
def samp (i : Nat) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Sampler (Addr L) State LiteralTranscript.Challenge :=
  LiteralTranscript.samp i P m

/-- The 40-row sampler over byte strings: R1's, unchanged. -/
def byteSamp (i : Nat) (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    Sampler Bytes State LiteralTranscript.Challenge :=
  LiteralByteSampler.samp i P m

/-- Agreement with R1 on rows 0 to 32 (indeed on every row: the definitions coincide). -/
theorem samp_r1 (i : Nat) (_hi : i < 33) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) : samp i P m = LiteralTranscript.samp i P m := rfl

theorem byteSamp_r1 (i : Nat) (_hi : i < 33) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) : byteSamp i P m = LiteralByteSampler.samp i P m := rfl

/-- Rows 33 to 39 are plain duplex rows: absorb at the current state with the
row's label and the message bytes, then squeeze and advance. -/
theorem row_final (i : Nat) (hlo : 33 ≤ i) (hhi : i < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : SelectedTranscriptParams.Message) :
    UnifiedSampler.samp p hD i P (.payload m) =
      DuplexSamplers.plain p (UnifiedSampler.absorb p i P m) i TranscriptView.liftChallenge :=
  UnifiedSampler.row_ordinary p hD i (by omega) (by omega) (by omega) P m

/-- The three oracle calls of a new row and its challenge. The challenge value
is the qm31 sampler of the squeezed block, the next state is the advance. -/
theorem final_eval (i : Nat) (hlo : 33 ≤ i) (hhi : i < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : SelectedTranscriptParams.Message) (H : Addr L → State) :
    let a := UnifiedSampler.absorb p i P m
    eval H (UnifiedSampler.samp p hD i P (.payload m)).toProgram =
      ([(a, H a), (squeezeA p (H a), H (squeezeA p (H a))),
        (advanceA p (H a), H (advanceA p (H a)))],
        (TranscriptView.Value.ordinary (R0P.SemSource.semChal (H (squeezeA p (H a)))),
          H (advanceA p (H a)))) := by
  intro a
  rw [row_final i hlo hhi P m, DuplexSamplers.plain_eval]
  simp only [TranscriptView.liftChallenge]
  rw [Labels.sigma_qm31 i (by omega)]

/-- The absorb frame of row `i` as bytes: state, 0, the label 160 + i, the
message bytes. No start frame and no reseed precede rows 33 to 39: the state
is the last challenge's state (`UnifiedSampler.stateOf`), which after row 32 is
row 32's advance output (Rust `Transcript::resume(hash, p.state)`,
fused.rs line 522, with `p.state = t.state` after `scalar_k(32, &[])`,
verifier.rs lines 97 and 101). -/
theorem absorb_bytes (i : Nat) (hi : i < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : SelectedTranscriptParams.Message) :
    (UnifiedSampler.absorb p i P m).toBytes =
      bytes (UnifiedSampler.stateOf p P) ++ [0, ⟨160 + i, by omega⟩] ++ m.val := by
  rw [UnifiedSampler.absorb, absorbA, Addr.toBytes_ofBytes]
  change bytes (UnifiedSampler.stateOf p P) ++ [0, UnifiedLabels.label i] ++ m.val = _
  have hl : UnifiedLabels.label i = ⟨160 + i, by omega⟩ := Fin.ext (Labels.label_val i hi)
  rw [hl]

theorem squeeze_bytes (s : State) : (squeezeA p s).toBytes = bytes s ++ [1] := by
  rw [squeezeA, Addr.toBytes_ofBytes]; rfl

theorem advance_bytes (s : State) : (advanceA p s).toBytes = bytes s ++ [2] := by
  rw [advanceA, Addr.toBytes_ofBytes]; rfl

/-! ## Payload bytes of the new rows -/

/-- Four little-endian bytes of `x mod 2^32` (Rust `u32::to_le_bytes`). -/
def u32le (x : Nat) : Bytes := PublicInitFrame.lengthBytes x

theorem u32le_length (x : Nat) : (u32le x).length = 4 := PublicInitFrame.lengthBytes_length x

/-- `WideExact::to_le_bytes`: the eight limbs, each four little-endian bytes,
in `to_limbs` order (wide_exact.rs lines 238-249 and 273-279). -/
def wideBytes (limbs : List Nat) : Bytes := limbs.flatMap u32le

theorem wideBytes_length (limbs : List Nat) : (wideBytes limbs).length = 4 * limbs.length := by
  induction limbs with
  | nil => rfl
  | cons x xs ih =>
      simp only [wideBytes, List.flatMap_cons, List.length_append, u32le_length,
        List.length_cons] at ih ⊢
      rw [ih]; ring

/-- The limb list of a canonical wide-field element: eight limbs below
P = 2^31 - 1 (`WideExact::from_limbs`, wide_exact.rs lines 207-211). -/
def Canonical (limbs : List Nat) : Prop := limbs.length = 8 ∧ ∀ x ∈ limbs, x < 2 ^ 31 - 1

/-- Row 33 payload, `claims_bytes(claim, rhs2)` (fused.rs lines 556-561). -/
def claimsPayload (claim rhs2 : List Nat) : Bytes := wideBytes claim ++ wideBytes rhs2

/-- Rows 34 to 39 payload: the 64 certificate bytes `c0 ‖ c2` of round b
(fused.rs lines 527-530), absorbed verbatim after both halves parsed
canonically; a canonical 32-byte half is `wideBytes` of its limbs. -/
def roundPayload (c0 c2 : List Nat) : Bytes := wideBytes c0 ++ wideBytes c2

theorem pair_length (x y : List Nat) (hx : x.length = 8) (hy : y.length = 8) :
    (wideBytes x ++ wideBytes y).length = 64 := by
  rw [List.length_append, wideBytes_length, wideBytes_length, hx, hy]

/-- The framed message of a new row: length bytes (64, 0, 0, 0), then the payload. -/
def finalMessage (payload : Bytes) (h : payload.length = 64) : SelectedTranscriptParams.Message :=
  ⟨PublicInitFrame.lengthBytes 64 ++ payload, by
    rw [List.length_append, PublicInitFrame.lengthBytes_length, h]
    norm_num [SelectedTranscriptParams.D]⟩

theorem length64 : PublicInitFrame.lengthBytes 64 = [64, 0, 0, 0] := by decide

/-- The complete absorb frame of a new row, byte for byte:
`state ‖ 0x00 ‖ 0xa0+i ‖ 64 0 0 0 ‖ payload` (transcript.rs line 20). -/
theorem final_absorb_bytes (i : Nat) (hi : i < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (payload : Bytes) (h : payload.length = 64) :
    (UnifiedSampler.absorb p i P (finalMessage payload h)).toBytes =
      bytes (UnifiedSampler.stateOf p P) ++ [0, ⟨160 + i, by omega⟩] ++
        [64, 0, 0, 0] ++ payload := by
  rw [absorb_bytes i hi]
  simp only [finalMessage, length64, List.append_assoc]

/-! The 40-row message schedule `valid40` is in AspisRows40Literal. -/

/-! ## Protocol -/

/-- The Aspis 40-row protocol: R1's `LiteralByteProtocol.protocol` with `r := 40`. -/
def protocol (decoder : LiteralByteProtocol.Decoder)
    (extractor : LiteralByteProtocol.Extractor :=
      fun pub _ => GenericNoHit.chooseWitness LiteralProtocol.relation pub) :
    FS2.Protocol LiteralTranscript.Public LiteralTranscript.Message LiteralTranscript.Challenge
      LiteralByteProtocol.Witness LiteralByteProtocol.Proof Bytes State where
  r := 40
  msg := fun pf i => pf i
  samp := LiteralByteSampler.samp
  decode := decoder
  extract := extractor

theorem protocol_r (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor) :
    (protocol D E).r = 40 := rfl

theorem protocol_samp (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor) :
    (protocol D E).samp = (LiteralByteProtocol.protocol D E).samp := rfl

theorem protocol_msg (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor) :
    (protocol D E).msg = (LiteralByteProtocol.protocol D E).msg := rfl

theorem protocol_decode (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor) :
    (protocol D E).decode = (LiteralByteProtocol.protocol D E).decode := rfl

theorem protocol_extract (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor) :
    (protocol D E).extract = (LiteralByteProtocol.protocol D E).extract := rfl

/-- Every transcript prefix of the 40-row protocol is R1's prefix of the same length. -/
theorem transcript_eq (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof)
    (n : Nat) :
    (protocol D E).transcript H pub pf n = (LiteralByteProtocol.protocol D E).transcript H pub pf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((protocol D E).transcript H pub pf n).ext (pf n)
          (eval H (LiteralByteSampler.samp n ((protocol D E).transcript H pub pf n)
            (pf n)).toProgram).2 =
        ((LiteralByteProtocol.protocol D E).transcript H pub pf n).ext (pf n)
          (eval H (LiteralByteSampler.samp n ((LiteralByteProtocol.protocol D E).transcript H pub pf n)
            (pf n)).toProgram).2
      rw [ih]

/-- Every chain of the 40-row protocol is R1's chain of the same row. -/
theorem chain_eq (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof)
    (i : Nat) :
    (protocol D E).chain H pub pf i = (LiteralByteProtocol.protocol D E).chain H pub pf i := by
  change LiteralByteSampler.samp i ((protocol D E).transcript H pub pf i) (pf i) =
    LiteralByteSampler.samp i ((LiteralByteProtocol.protocol D E).transcript H pub pf i) (pf i)
  rw [transcript_eq]

#print axioms hD
#print axioms samp_r1
#print axioms byteSamp_r1
#print axioms row_final
#print axioms final_eval
#print axioms absorb_bytes
#print axioms squeeze_bytes
#print axioms advance_bytes
#print axioms wideBytes_length
#print axioms pair_length
#print axioms length64
#print axioms final_absorb_bytes
#print axioms protocol_r
#print axioms protocol_samp
#print axioms transcript_eq
#print axioms chain_eq

/-! ## Interface for the row densities (AspisRowDensitySampler)

Its `combining_unified_density` / `round_unified_density` take a unified-sampler
instance `p`, a row `i ≠ 31`, `UnifiedSampler.messageValid i m`, and
`hσ : ∀ s, rhoOf (p.σ i s) = qm31Sample s`. The 40-row sampler is R1's with
`p = SelectedTranscriptParams.params`; the three facts for rows 33 to 39: -/

theorem final_ne31 (i : Nat) (hlo : 33 ≤ i) : i ≠ 31 := by omega

theorem final_messageValid (i : Nat) (hlo : 33 ≤ i) (m : SelectedTranscriptParams.Message) :
    UnifiedSampler.messageValid i (.payload m) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  trivial

theorem final_sigma_rho (i : Nat) (hlo : 32 ≤ i) (s : State) :
    SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s := by
  rw [Labels.sigma_qm31 i hlo]
  exact SelectedChallengeMap.semChal_re s

/-- The 64 payload bytes of a new row's message (claim ‖ rhs2 for row 33,
c0 ‖ c2 for rounds 34 to 39), read back from the framed message; `none` if the
message is not a 64-byte frame. This is the read a row-33..39 bad set uses. -/
def payloadOf (m : TranscriptView.Message SelectedTranscriptParams.Message) : Option Bytes :=
  match m with
  | .payload b => if b.val.take 4 = [64, 0, 0, 0] ∧ b.val.length = 68 then some (b.val.drop 4) else none
  | .initial _ => none

theorem payloadOf_final (payload : Bytes) (h : payload.length = 64) :
    payloadOf (.payload (finalMessage payload h)) = some payload := by
  have hl : (PublicInitFrame.lengthBytes 64).length = 4 := PublicInitFrame.lengthBytes_length 64
  simp only [payloadOf, finalMessage]
  rw [if_pos]
  · rw [List.drop_left' hl]
  · constructor
    · rw [List.take_left' hl, length64]
    · rw [List.length_append, hl, h]

#print axioms final_messageValid
#print axioms final_sigma_rho
#print axioms payloadOf_final

end AspisRows40.Protocol
end
