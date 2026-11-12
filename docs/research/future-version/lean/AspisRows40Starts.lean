import AspisHonestBudgetBase
import AspisLib_Recorded
import AspisWeightedFirstRead
import AspisRows40Protocol
import AspisRows40Decoder

/-! Aspis one-transaction verifier: decoded starts of the 40-row honest sampler.

The byte-level Aspis decoder `decAspis fin` is R1's byte decoder
`RecordedBinaryExperimentBin.dec`, extended on the frames of rows 33 to 39 by a
final-sumcheck byte decoder `fin n` (a parameter: its construction and law are
the density obligation, not this file's). It is `dec` wherever `dec` decodes
(`decAspis_of_r1`), and on an absorb frame with label row 33 to 39, where R1's
`dec` is `none` (`dec_none_of_finalRow`), it is `fin n` (`decAspis_final`).

Counting results, for EVERY `fin`:
* `sampler_starts`: every row n of R1's sampler (now read for n < 40)
  contributes at most `1 + [n = 26]` decoded first reads (R1's
  `BinHonestQueryBudget.sampler_starts`, re-proved for `decAspis`);
* `final_row_weight`: for 33 ≤ n < 40 the decoded first reads of row n are
  exactly the indicator of its absorb frame (fresh and decoded), for any
  weight `wt`; the frame's dispatch row is n (`finalRow_absorb`);
* `verifier_starts`: the 40-row verifier has at most 41 decoded first reads. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Starts
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1
open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound
open BinHonestStartFrames AspisHonestBudgetBase
open CanonicalAddressEmbedding
open AspisPerStep.WeightedFirstRead

abbrev BDec := Dec LiteralTranscript.Public LiteralTranscript.Message
  LiteralTranscript.Challenge Bytes State (List State)

/-! ## The new rows' frames, by bytes -/

/-- `parseAbsorb` on raw bytes. -/
def parseBytes (b : Bytes) : Option (State × AspisV8R19.DuplexFrames.Byte × Bytes) :=
  if 34 ≤ b.length ∧ b.getD 32 1 = 0 then some (stateOfBytes b, b.getD 33 0, b.drop 34) else none

theorem parseAbsorb_eq (a : Addr L) : parseAbsorb a = parseBytes a.toBytes := rfl

/-- The row of an absorb frame whose label is one of the seven new rows. -/
def finalRow (a : Bytes) : Option Nat :=
  (parseBytes a).bind fun (_, label, _) =>
    if 33 ≤ UnifiedLabels.row label ∧ UnifiedLabels.row label < 40 then
      some (UnifiedLabels.row label) else none

theorem finalRow_sound (a : Bytes) (n : Nat) (h : finalRow a = some n) :
    ∃ s label data, parseBytes a = some (s, label, data) ∧
      UnifiedLabels.row label = n ∧ 33 ≤ n ∧ n < 40 := by
  unfold finalRow at h
  rcases hp : parseBytes a with _ | ⟨s, label, data⟩
  · rw [hp] at h; cases h
  · rw [hp, Option.bind_some] at h
    dsimp only at h
    split at h
    · rename_i hc
      injection h with h
      exact ⟨s, label, data, by simp [hp], h, h ▸ hc.1, h ▸ hc.2⟩
    · cases h

/-- The dispatch row of a frame of row `n < 40`. (Labels are `(160 + n) mod 256`,
so the statement needs `n < 40`: row 289 would carry row 33's label.) -/
theorem finalRow_absorb (s : State) (n : Nat) (hn : n < 40) (data : Bytes) (hd : data.length ≤ p.D) :
    finalRow (absorbA p s (p.lbl n) data hd).toBytes =
      if 33 ≤ n then some n else none := by
  unfold finalRow
  rw [← parseAbsorb_eq, parseAbsorb_absorbA, Option.bind_some]
  dsimp only
  rw [Labels.params_lbl, Labels.row_label n hn]
  by_cases h : 33 ≤ n
  · rw [if_pos ⟨h, hn⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem finalRow_short (a : Bytes) (h : a.length < 34) : finalRow a = none := by
  unfold finalRow parseBytes
  rw [if_neg (by omega)]
  rfl

/-- R1's byte decoder rejects every frame of a new row. -/
theorem dec_none_of_finalRow (a : Bytes) (T : Table Bytes State) (n : Nat)
    (h : finalRow a = some n) : dec a T = none := by
  obtain ⟨s, label, data, hp, hrow, hlo, _⟩ := finalRow_sound a n h
  unfold RecordedBinaryExperimentBin.dec RawAdaptiveLiteralDecoder.decode
  cases hs : RawFullPublicSelection.select a T with
  | none => rfl
  | some pub =>
      simp only [Option.bind_some]
      unfold RawLiteralDecoderDensity.decode RawUnifiedDecoder.decode
      cases hc : CanonicalRawTrace.decode L a with
      | none => rfl
      | some ac =>
          have hb : ac.1.toBytes = a := (CanonicalRawTrace.decode_iff L a ac).1 hc
          have hpa : parseAbsorb ac.1 = some (s, label, data) := by
            rw [parseAbsorb_eq, hb, hp]
          have hu := Decoder.r1_none_of_final p
            (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
            pub ac.1 (RawBoundedTrace.table L T) s label data hpa (by omega)
          simp only [Option.bind_some]
          rw [RawUnifiedDecoder.atCanonical_none p _ pub ac T hu]
          rfl

/-! ## The Aspis byte decoder -/

def decAspis (fin : Nat → BDec) : BDec := fun a T =>
  match dec a T with
  | some r => some r
  | none =>
      match finalRow a with
      | some n => fin n a T
      | none => none

theorem decAspis_of_r1 (fin : Nat → BDec) (a : Bytes) (T : Table Bytes State)
    (h : dec a T ≠ none) : decAspis fin a T = dec a T := by
  unfold decAspis
  cases hd : dec a T with
  | none => exact absurd hd h
  | some r => rfl

theorem decAspis_final (fin : Nat → BDec) (a : Bytes) (T : Table Bytes State) (n : Nat)
    (h : finalRow a = some n) : decAspis fin a T = fin n a T := by
  unfold decAspis
  rw [dec_none_of_finalRow a T n h]
  simp only [h]

theorem decAspis_none (fin : Nat → BDec) (a : Bytes) (T : Table Bytes State)
    (hd : dec a T = none) (hf : finalRow a = none) : decAspis fin a T = none := by
  unfold decAspis
  rw [hd]
  simp only [hf]

theorem aspis_squeeze (fin : Nat → BDec) (s : State) (T : Table Bytes State) :
    decAspis fin (squeezeA p s).toBytes T = none :=
  decAspis_none fin _ T (reject_squeeze s T)
    (finalRow_short _ (by simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]))

theorem aspis_advance (fin : Nat → BDec) (s : State) (T : Table Bytes State) :
    decAspis fin (advanceA p s).toBytes T = none :=
  decAspis_none fin _ T (reject_advance s T)
    (finalRow_short _ (by simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]))

theorem aspis_row_zero (fin : Nat → BDec) (s : State) (T : Table Bytes State) :
    decAspis fin (PublicInitFrame.row0 p (by norm_num [p, SelectedTranscriptParams.params,
      SelectedTranscriptParams.D]) s).toBytes T = none := by
  apply decAspis_none fin _ T (reject_row_zero s T)
  have h := finalRow_absorb s 0 (by omega) PublicInitFrame.emptyRecord
    (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D,
      PublicInitFrame.emptyRecord])
  rw [if_neg (by omega)] at h
  exact h

/-! ## Starts of the honest sampler rows -/

theorem query_tail_zero {C : Type} (fin : Nat → BDec) (H : Addr L → State)
    (out : List State → List State → C) (n : Nat) (s : State)
    (bs xs : List State) (T : Table Bytes State) :
    decoderFirstReads (decAspis fin) T
      (raw (eval H (QuerySampler.chain p out n s bs xs).toProgram).1) = 0 := by
  induction n generalizing s bs xs T with
  | zero => rfl
  | succ n ih =>
    simp only [QuerySampler.chain, Sampler.toProgram, eval, raw, List.map_cons,
      decoderFirstReads, aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
      and_false, if_false, zero_add]
    exact ih _ _ _ _

/-- R1's per-row start bound for the Aspis decoder, every row. -/
theorem sampler_starts (fin : Nat → BDec) (H : Addr L → State) (n : Nat)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message)
    (T : Table Bytes State) :
    decoderFirstReads (decAspis fin) T (raw (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) n P m).toProgram).1)
      ≤ 1 + if n = 26 then 1 else 0 := by
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
        aspis_row_zero, aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
        and_false, if_false, zero_add]
      split <;> norm_num
    | payload msg =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstReads, aspis_squeeze]
  | succ n =>
    cases m with
    | initial root =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstReads, aspis_squeeze]
    | payload msg =>
      by_cases h26 : n+1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
          aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
          and_false, if_false, zero_add]
        split <;> split <;> norm_num
      · by_cases h31 : n+1 = 31
        · rw [h31, UnifiedSampler.row_query]
          change (if T _ = none ∧ decAspis fin _ T ≠ none then 1 else 0) +
            decoderFirstReads (decAspis fin) _
              (raw (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1) ≤ _
          rw [query_tail_zero]
          split <;> norm_num
        · rw [UnifiedSampler.row_ordinary p _ (n+1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
            aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
            and_false, if_false, zero_add, h26]
          split <;> norm_num

/-- A new row (33 to 39), weighted by any `wt`: its decoded first reads are
exactly its absorb frame's, when that frame is fresh and decoded. The frame's
dispatch row is `n` (`finalRow_absorb`), and there `decAspis fin = fin n`. -/
theorem final_row_weight (fin : Nat → BDec) (wt : Bytes → Table Bytes State → ℚ)
    (H : Addr L → State) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State) :
    let a := (UnifiedSampler.absorb p n P msg).toBytes
    decoderFirstWeight (decAspis fin) wt T (raw (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        n P (.payload msg)).toProgram).1) =
      (if T a = none ∧ fin n a T ≠ none then wt a T else 0) := by
  intro a
  have hf : finalRow a = some n := by
    have h := finalRow_absorb (UnifiedSampler.stateOf p P) n hhi (p.enc msg) (p.encLen msg)
    rw [if_pos hlo] at h
    exact h
  rw [Protocol.row_final n hlo hhi P msg, DuplexSamplers.plain_eval]
  simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
    aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
    and_false, if_false, add_zero]
  change (if T a = none ∧ ¬ decAspis fin a T = none then wt a T else 0) = _
  rw [decAspis_final fin a T n hf]

/-- The same in counts. -/
theorem final_row_starts (fin : Nat → BDec)
    (H : Addr L → State) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (msg : SelectedTranscriptParams.Message) (T : Table Bytes State) :
    let a := (UnifiedSampler.absorb p n P msg).toBytes
    decoderFirstReads (decAspis fin) T (raw (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
        n P (.payload msg)).toProgram).1) =
      (if T a = none ∧ fin n a T ≠ none then 1 else 0) := by
  intro a
  have hf : finalRow a = some n := by
    have h := finalRow_absorb (UnifiedSampler.stateOf p P) n hhi (p.enc msg) (p.encLen msg)
    rw [if_pos hlo] at h
    exact h
  rw [Protocol.row_final n hlo hhi P msg, DuplexSamplers.plain_eval]
  simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
    aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
    and_false, if_false, add_zero]
  change (if T a = none ∧ ¬ decAspis fin a T = none then 1 else 0) = _
  rw [decAspis_final fin a T n hf]

/-! ## The 40-row verifier -/

def verifier (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool) :
    LiteralTranscript.Public → RawCutProverCompiler.Proof → Program Bytes State Bool :=
  FS2.verifier (Protocol.protocol D) (RawCutTranscriptRun.decisionOnBytes d)

theorem row_starts (fin : Nat → BDec) (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (n : Nat) (T : Table Bytes State) :
    decoderFirstReads (decAspis fin) T
      (eval H ((Protocol.protocol D).chain H pub pf n).toProgram).1 ≤
        1 + if n = 26 then 1 else 0 := by
  change decoderFirstReads (decAspis fin) T
    (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1 ≤ _
  rw [LiteralByteSampler.eval_eq]
  exact sampler_starts fin (fun a => H a.toBytes) n _ _ T

theorem rows_bound (fin : Nat → BDec) (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (ns : List Nat) (hn : ns.Nodup) (T : Table Bytes State) :
    decoderFirstReads (decAspis fin) T
      (ns.map (fun n => (eval H ((Protocol.protocol D).chain H pub pf n).toProgram).1)).flatten ≤
        ns.length + if 26 ∈ ns then 1 else 0 := by
  induction ns generalizing T with
  | nil => simp [decoderFirstReads]
  | cons n ns ih =>
    rw [List.map_cons, List.flatten_cons, decoderFirstReads_append]
    have hb := row_starts fin D H pub pf n T
    have ht := ih (List.nodup_cons.mp hn).2
      (applyTrace T (eval H ((Protocol.protocol D).chain H pub pf n).toProgram).1)
    have hn' := (List.nodup_cons.mp hn).1
    simp only [List.length_cons, List.mem_cons]
    by_cases he : n = 26
    · subst n
      simp only [true_or, if_true] at *
      have hm : 26 ∉ ns := hn'
      simp only [hm, if_false] at ht
      omega
    · by_cases hm : 26 ∈ ns <;> simp_all only [if_false, if_true, eq_comm, false_or] <;> omega

/-- The 40-row verifier: at most 40 + 1 decoded first reads (the extra one is
the row-26 reseed frame, as in R1). -/
theorem verifier_starts (fin : Nat → BDec) (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstReads (decAspis fin) T (eval H (verifier D d pub pf)).1 ≤ 41 := by
  unfold verifier
  rw [FS2.verifier_eval]
  exact (rows_bound fin D H pub pf (List.range 40) List.nodup_range T).trans (by simp)

#print axioms parseAbsorb_eq
#print axioms finalRow_sound
#print axioms finalRow_absorb
#print axioms finalRow_short
#print axioms dec_none_of_finalRow
#print axioms decAspis_of_r1
#print axioms decAspis_final
#print axioms decAspis_none
#print axioms aspis_squeeze
#print axioms aspis_advance
#print axioms aspis_row_zero
#print axioms query_tail_zero
#print axioms sampler_starts
#print axioms final_row_weight
#print axioms final_row_starts
#print axioms row_starts
#print axioms rows_bound
#print axioms verifier_starts

end AspisRows40.Starts
end
