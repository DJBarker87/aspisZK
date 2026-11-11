import LiteralDecoderEnrichment
import AspisRows40Protocol

/-! Aspis one-transaction verifier: the 40-row literal transcript layer.

R1's literal carrier is already total in the row number: the message type
`LiteralTranscript.Message` has the constructor `.payload` for word-free rows,
`LiteralTranscript.samp` is defined for every row, and the enrichment maps
`LiteralDecoderEnrichment.message` / `rounds` / `restorePrefix` send a payload
message at any row other than 2 and 30 to itself. The ONLY part hard-wired to
33 is the schedule `LiteralTranscript.valid` (payload rows `i < 33`). So the
40-row literal layer is R1's carrier with a new schedule `valid40`, which is
R1's below 33 and, on rows 33 to 39, requires a payload message that is a
framed 64-byte payload (`Protocol.payloadOf`). No new message type is needed.

Also here: the prefix lemma used by the acceptance link (the first 33 rounds
of an Aspis transcript are R1's transcript of 33 rounds). -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Literal
open FS FS2
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The 40-row constructor schedule. -/
def valid40 (n : Nat) (m : LiteralTranscript.Message) : Prop :=
  if n < 33 then LiteralTranscript.valid n m
  else n < 40 ∧ (∃ b, m = .payload b) ∧ (Protocol.payloadOf (LiteralTranscript.erase m)).isSome

theorem valid40_r1 (n : Nat) (hn : n < 33) (m : LiteralTranscript.Message) :
    valid40 n m ↔ LiteralTranscript.valid n m := by
  simp only [valid40, if_pos hn]

theorem valid40_final (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) (payload : Bytes)
    (h : payload.length = 64) :
    valid40 n (.payload (Protocol.finalMessage payload h)) := by
  simp only [valid40, if_neg (by omega : ¬ n < 33)]
  refine ⟨hhi, ⟨_, rfl⟩, ?_⟩
  change (Protocol.payloadOf (.payload (Protocol.finalMessage payload h))).isSome = true
  rw [Protocol.payloadOf_final]
  rfl

theorem valid40_final_payload (n : Nat) (hlo : 33 ≤ n) (m : LiteralTranscript.Message)
    (h : valid40 n m) : ∃ b pl, m = .payload b ∧ Protocol.payloadOf (.payload b) = some pl := by
  simp only [valid40, if_neg (by omega : ¬ n < 33)] at h
  obtain ⟨_, ⟨b, rfl⟩, hs⟩ := h
  obtain ⟨pl, hpl⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨b, pl, rfl, hpl⟩

/-- Enrichment leaves the new rows' messages unchanged. -/
theorem enrich_final (w : CanonicalCutEnrichedTranscript.Words) (n : Nat) (hlo : 33 ≤ n)
    (b : LiteralTranscript.BytesMessage) :
    LiteralDecoderEnrichment.message w n (.payload b) = .payload b := by
  simp only [LiteralDecoderEnrichment.message, if_neg (by omega : n ≠ 2),
    if_neg (by omega : n ≠ 30)]

theorem erase_payload (b : LiteralTranscript.BytesMessage) :
    LiteralTranscript.erase (.payload b) = .payload b := rfl

/-! ## Prefix lemma -/

section Generic
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

theorem transcript_statement (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf)
    (n : Nat) : (pr.transcript H x π n).statement = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem transcript_length (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf)
    (n : Nat) : (pr.transcript H x π n).rounds.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((pr.transcript H x π n).rounds ++ [_]).length = n + 1
      rw [List.length_append, ih]
      rfl

theorem transcript_take (pr : FS2.Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf)
    (k : Nat) : ∀ n, k ≤ n → (pr.transcript H x π n).rounds.take k = (pr.transcript H x π k).rounds := by
  intro n
  induction n with
  | zero =>
      intro hk
      have : k = 0 := by omega
      subst this
      rfl
  | succ n ih =>
      intro hk
      by_cases he : k = n + 1
      · subst he
        rw [List.take_of_length_le (by rw [transcript_length])]
      · change ((pr.transcript H x π n).rounds ++ [_]).take k = _
        rw [List.take_append_of_le_length (by rw [transcript_length]; omega)]
        exact ih (by omega)
end Generic

/-- The first 33 rounds of every Aspis transcript prefix of length at least 33
are R1's transcript of 33 rounds (same statement, same rounds). -/
theorem transcript_take33 (D : LiteralByteProtocol.Decoder) (E : LiteralByteProtocol.Extractor)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof)
    (n : Nat) (hn : 33 ≤ n) :
    ((Protocol.protocol D E).transcript H pub pf n).statement =
        ((LiteralByteProtocol.protocol D E).transcript H pub pf 33).statement ∧
      ((Protocol.protocol D E).transcript H pub pf n).rounds.take 33 =
        ((LiteralByteProtocol.protocol D E).transcript H pub pf 33).rounds := by
  constructor
  · rw [transcript_statement, transcript_statement]
  · rw [transcript_take _ H pub pf 33 n hn, Protocol.transcript_eq]

/-- With R1's validity: a proof valid for the 40-row schedule is valid for R1's
schedule on rows 0 to 32. -/
theorem valid40_take33 (pf : LiteralByteProtocol.Proof) (h : ∀ i < 40, valid40 i (pf i)) :
    ∀ i < 33, LiteralTranscript.valid i (pf i) :=
  fun i hi => (valid40_r1 i hi (pf i)).1 (h i (by omega))

#print axioms valid40_r1
#print axioms valid40_final
#print axioms valid40_final_payload
#print axioms enrich_final
#print axioms transcript_statement
#print axioms transcript_length
#print axioms transcript_take
#print axioms transcript_take33
#print axioms valid40_take33

end AspisRows40.Literal
end
