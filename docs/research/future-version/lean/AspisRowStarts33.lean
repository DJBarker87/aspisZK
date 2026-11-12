import AspisRowStarts
import BinHonestQueryBudget

/-! Split from `AspisRowStarts` (text unchanged): the 33-row theorems about R1's
decoder, used only by `AspisChargedWeight`, `AspisChargedHitMass` and
`AspisChargedHitMassCheck`, not by the 40-row chain.

Per-step accounting, piece (c), verifier part: the weighted count of the
decoder starts that R1's 33 honest sampler rows contribute, for every
incoming table, with each start charged by piece (b)'s `charge`.

Kind of result: a deterministic counting theorem about R1's sampler programs
(the same level as R1's `BinHonestQueryBudget.verifier_starts`, which it
refines). Row n contributes at most `classCap n`; row 26 additionally reads
the opening reseed frame, charged `capMax` (conservative: its decoded row is
not determined here). -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.RowStarts
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.TranscriptView
open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound
open BinHonestStartFrames BinHonestQueryBudget
open CanonicalAddressEmbedding
open AspisPerStep.RowCharge AspisPerStep.WeightedFirstRead
attribute [local instance] Classical.propDecidable

private theorem ite_le {c : Prop} {d : Decidable c} (x y : ℚ) (hx : x ≤ y) (hy : 0 ≤ y) :
    @ite ℚ c d x 0 ≤ y := by
  split_ifs
  · exact hx
  · exact hy

private theorem weight_le_zero_of_count (T : Table Bytes State) (tr : List (Bytes × State))
    (h : decoderFirstReads dec T tr = 0) : decoderFirstWeight dec wt T tr ≤ 0 := by
  have := decoderFirstWeight_le_count_mul dec wt capMax wt_le_capMax T tr
  rw [h] at this
  simpa using this

/-- Weighted analogue of `BinHonestQueryBudget.sampler_starts`. -/
theorem sampler_weight (H : Addr L → State) (n : Nat) (hn : n < 33)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message)
    (T : Table Bytes State) :
    decoderFirstWeight dec wt T (raw (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) n P m).toProgram).1)
      ≤ rowCharge n := by
  have hrc : classCap n ≤ rowCharge n := by
    unfold rowCharge
    have := capMax_nonneg
    split_ifs <;> linarith
  have hrc0 : 0 ≤ rowCharge n := (classCap_nonneg n).trans hrc
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
        reject_row_zero, reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
        and_false, if_false, add_zero]
      exact ite_le _ _ ((wt_init _ _ _ _).trans hrc) hrc0
    | payload msg =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstWeight, reject_squeeze] <;> linarith [hrc0]
  | succ k =>
    cases m with
    | initial root =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstWeight, reject_squeeze] <;> linarith [hrc0]
    | payload msg =>
      by_cases h26 : k + 1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
          reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
          and_false, if_false, zero_add, add_zero]
        unfold rowCharge
        rw [if_pos rfl]
        apply add_le_add
        · exact ite_le _ _ (wt_absorb (UnifiedSampler.stateOf p P) 26 (by omega)
            (p.enc msg) (p.encLen msg) _) (classCap_nonneg 26)
        · exact ite_le _ _ (wt_le_capMax _ _) capMax_nonneg
      · by_cases h31 : k + 1 = 31
        · rw [h31, UnifiedSampler.row_query]
          rw [h31] at hrc hrc0
          change (if T _ = none ∧ dec _ T ≠ none then wt _ T else 0) +
            decoderFirstWeight dec wt _
              (raw (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1) ≤ _
          have key : ∀ x y : ℚ, x ≤ rowCharge 31 → y ≤ 0 → x + y ≤ rowCharge 31 := by
            intro x y hx hy; linarith
          apply key
          · exact ite_le _ _ ((wt_absorb (UnifiedSampler.stateOf p P) 31 (by omega)
              (p.enc msg) (p.encLen msg) _).trans hrc) hrc0
          · apply weight_le_zero_of_count
            exact query_tail_zero _ _ _ _ _ _ _
        · rw [UnifiedSampler.row_ordinary p _ (k + 1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
            reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
            and_false, if_false, add_zero]
          exact ite_le _ _ ((wt_absorb (UnifiedSampler.stateOf p P) (k + 1) hn
            (p.enc msg) (p.encLen msg) _).trans hrc) hrc0

/-- Weighted analogue of `BinHonestQueryBudget.row_starts`. -/
theorem row_weight (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (n : Nat) (hn : n < 33) (T : Table Bytes State) :
    decoderFirstWeight dec wt T
      (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1 ≤ rowCharge n := by
  change decoderFirstWeight dec wt T
    (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1 ≤ _
  rw [LiteralByteSampler.eval_eq]
  exact sampler_weight (fun a => H a.toBytes) n hn _ _ T

/-- Weighted analogue of `BinHonestQueryBudget.rows_bound`. -/
theorem rows_weight (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (ns : List Nat) (hns : ∀ n ∈ ns, n < 33) (T : Table Bytes State) :
    decoderFirstWeight dec wt T
      (ns.map (fun n => (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1)).flatten ≤
        (ns.map rowCharge).sum := by
  induction ns generalizing T with
  | nil => simp [decoderFirstWeight]
  | cons n ns ih =>
    rw [List.map_cons, List.flatten_cons, decoderFirstWeight_append, List.map_cons, List.sum_cons]
    have hb := row_weight D H pub pf n (hns n (List.mem_cons_self ..)) T
    have ht := ih (fun k hk => hns k (List.mem_cons_of_mem n hk))
      (applyTrace T (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1)
    linarith

/-- Piece (c), verifier part (weighted analogue of `BinHonestQueryBudget.verifier_starts`). -/
theorem verifier_weight (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstWeight dec wt T (eval H (verifier D d pub pf)).1 ≤ verifierCharge := by
  unfold RawCutProverCompiler.verifier
  rw [FS2.verifier_eval]
  exact rows_weight D H pub pf (List.range 33) (fun n hn => List.mem_range.mp hn) T

#print axioms sampler_weight
#print axioms rows_weight
#print axioms verifier_weight
end AspisPerStep.RowStarts
end
