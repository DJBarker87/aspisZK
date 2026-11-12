import AspisCharge40
import AspisRowStarts
import AspisRows40Starts

/-! Plan item 10: the weighted start count of the Aspis 40-row verifier
(41 starts), each start charged by piece (b)'s `charge40`.

Row n < 33 contributes at most `classCap n` (row 26 additionally reads the
reseed frame, charged `capMax`, the largest cap over all 40 rows: the reseed
frame can parse as a frame of any row 0 to 39); row 33 at most `capLambda`;
rows 34 to 39 at most `capRound`. Only upper bounds are used, so "exactly
one start per new row" is not needed.

Kind of result: deterministic counting theorem about the 40-row sampler
programs (the level of R1's `BinHonestQueryBudget.verifier_starts`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace AspisRowStarts40
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.TranscriptView
open AspisR1.AspisLib.RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound
open BinHonestStartFrames AspisHonestBudgetBase
open CanonicalAddressEmbedding
open AspisPerStep.WeightedFirstRead AspisPerStep.RowCharge AspisPerStep.RowStarts
open AspisCharge40 AspisRowDensity.QM31
open AspisRows40.Starts
attribute [local instance] Classical.propDecidable

/-! ## Charges of the frames -/

theorem finalCap_le_capMax (n : Nat) : finalCap n ≤ capMax := by
  have h32 : LiteralClassifier.budget 32 ≤ capMax := by
    unfold capMax
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))
  rw [AspisRowDensity.Caps.budget32_eq_capPair] at h32
  unfold finalCap
  split_ifs
  · exact (capLambda_le_capRound.trans capRound_le_capPair).trans h32
  · exact capRound_le_capPair.trans h32

theorem charge40_le_capMax (a : Bytes) (T : Table Bytes State) : charge40 a T ≤ capMax := by
  unfold charge40
  split
  · exact finalCap_le_capMax _
  · exact wt_le_capMax a T

theorem finalCap_nonneg (n : Nat) : 0 ≤ finalCap n := by
  have hl : 0 ≤ capLambda := by unfold capLambda perElem; positivity
  have hr : 0 ≤ capRound := by unfold capRound perElem; positivity
  unfold finalCap
  split_ifs
  · exact hl
  · exact hr

theorem charge40_nonneg (a : Bytes) (T : Table Bytes State) : 0 ≤ charge40 a T := by
  unfold charge40
  split
  · exact finalCap_nonneg _
  · exact wt_nonneg a T

/-- An R1 absorb frame of row n < 33: R1's charge. -/
theorem charge40_absorb (s : State) (n : Nat) (hn : n < 33) (data : Bytes) (hd : data.length ≤ p.D)
    (T : Table Bytes State) :
    charge40 (absorbA p s (p.lbl n) data hd).toBytes T ≤ classCap n := by
  have hf : finalRow (absorbA p s (p.lbl n) data hd).toBytes = none := by
    rw [finalRow_absorb s n (by omega) data hd, if_neg (by omega)]
  unfold charge40
  rw [hf]
  exact wt_absorb s n hn data hd T

/-- The initialisation frame: R1's charge. -/
theorem charge40_init (pubBytes : Bytes) (hL : 75 + pubBytes.length ≤ L) (c1 : State)
    (T : Table Bytes State) :
    charge40 (PublicInitFrame.addr pubBytes hL c1).toBytes T ≤ classCap 0 := by
  have hf : finalRow (PublicInitFrame.addr pubBytes hL c1).toBytes = none := by
    have htag : (PublicInitFrame.addr pubBytes hL c1).toBytes.getD 32
        (1 : AspisV8R19.DuplexFrames.Byte) = 84 := by
      rw [PublicInitFrame.addr_bytes]
      simp [PublicInitFrame.domain, PublicInitFrame.lengthBytes]
    unfold finalRow parseBytes
    rw [if_neg (by
      intro hc
      have hbad := hc.2
      rw [htag] at hbad
      exact (by decide : (84 : AspisV8R19.DuplexFrames.Byte) ≠ 0) hbad)]
    rfl
  unfold charge40
  rw [hf]
  exact wt_init pubBytes hL c1 T

/-! ## One sampler row -/

/-- Weighted charge of row n of the 40-row verifier. -/
def rowCharge40 (n : Nat) : ℚ := if n < 33 then rowCharge n else finalCap n

theorem rowCharge40_26 : rowCharge40 26 = classCap 26 + capMax := by
  unfold rowCharge40 rowCharge
  simp

private theorem ite_le {c : Prop} {d : Decidable c} (x y : ℚ) (hx : x ≤ y) (hy : 0 ≤ y) :
    @ite ℚ c d x 0 ≤ y := by
  split_ifs
  · exact hx
  · exact hy

private theorem weight_le_zero_of_count (T : Table Bytes State) (tr : List (Bytes × State))
    (h : decoderFirstReads AspisRows40.FinalStarts.decFinal T tr = 0) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T tr ≤ 0 := by
  have := decoderFirstWeight_le_count_mul AspisRows40.FinalStarts.decFinal charge40 capMax
    charge40_le_capMax T tr
  rw [h] at this
  simpa using this

/-- Weighted per-row bound for the 40-row decoder. -/
theorem sampler_weight40 (H : Addr L → State) (n : Nat) (hn : n < 40)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message)
    (T : Table Bytes State) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T
      (raw (eval H (UnifiedSampler.samp p
        (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) n P m).toProgram).1)
      ≤ rowCharge40 n := by
  unfold AspisRows40.FinalStarts.decFinal
  have hrc0 : 0 ≤ rowCharge40 n := by
    unfold rowCharge40 rowCharge
    have := capMax_nonneg
    have := classCap_nonneg n
    have := finalCap_nonneg n
    split_ifs <;> linarith
  by_cases h33 : n < 33
  · have hrc : classCap n ≤ rowCharge40 n := by
      unfold rowCharge40 rowCharge
      rw [if_pos h33]
      have := capMax_nonneg
      split_ifs <;> linarith
    cases n with
    | zero =>
      cases m with
      | initial root =>
        rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
        simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
          aspis_row_zero, aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
          and_false, if_false, add_zero]
        exact ite_le _ _ ((charge40_init _ _ _ _).trans hrc) hrc0
      | payload msg =>
        simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
          raw, decoderFirstWeight, aspis_squeeze] <;> linarith [hrc0]
    | succ k =>
      cases m with
      | initial root =>
        simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
          raw, decoderFirstWeight, aspis_squeeze] <;> linarith [hrc0]
      | payload msg =>
        by_cases h26 : k + 1 = 26
        · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
          simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
            aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
            and_false, if_false, zero_add, add_zero]
          rw [rowCharge40_26]
          apply add_le_add
          · exact ite_le _ _ (charge40_absorb (UnifiedSampler.stateOf p P) 26 (by omega)
              (p.enc msg) (p.encLen msg) _) (classCap_nonneg 26)
          · exact ite_le _ _ (charge40_le_capMax _ _) capMax_nonneg
        · by_cases h31 : k + 1 = 31
          · rw [h31, UnifiedSampler.row_query]
            rw [h31] at hrc hrc0
            change (if T _ = none ∧ decAspis AspisRows40.FinalByte.fin _ T ≠ none then charge40 _ T else 0) +
              decoderFirstWeight (decAspis AspisRows40.FinalByte.fin) charge40 _
                (raw (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1) ≤ _
            have key : ∀ x y : ℚ, x ≤ rowCharge40 31 → y ≤ 0 → x + y ≤ rowCharge40 31 := by
              intro x y hx hy; linarith
            apply key
            · exact ite_le _ _ ((charge40_absorb (UnifiedSampler.stateOf p P) 31 (by omega)
                (p.enc msg) (p.encLen msg) _).trans hrc) hrc0
            · apply weight_le_zero_of_count
              unfold AspisRows40.FinalStarts.decFinal
              exact AspisRows40.Starts.query_tail_zero AspisRows40.FinalByte.fin _ _ _ _ _ _ _
          · rw [UnifiedSampler.row_ordinary p _ (k + 1) (by omega) h26 h31,
              DuplexSamplers.plain_eval]
            simp only [raw, List.map_cons, List.map_nil, decoderFirstWeight,
              aspis_squeeze, aspis_advance, ne_eq, not_true_eq_false,
              and_false, if_false, add_zero]
            exact ite_le _ _ ((charge40_absorb (UnifiedSampler.stateOf p P) (k + 1) h33
              (p.enc msg) (p.encLen msg) _).trans hrc) hrc0
  · have hlo : 33 ≤ n := by omega
    have hrc : finalCap n ≤ rowCharge40 n := by
      unfold rowCharge40; rw [if_neg h33]
    cases m with
    | initial root =>
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstWeight, aspis_squeeze] <;> linarith [hrc0]
    | payload msg =>
      have h := final_row_weight AspisRows40.FinalByte.fin charge40 H n hlo hn P msg T
      have hf : finalRow (UnifiedSampler.absorb p n P msg).toBytes = some n := by
        have h' := finalRow_absorb (UnifiedSampler.stateOf p P) n hn (p.enc msg) (p.encLen msg)
        rw [if_pos hlo] at h'
        exact h'
      have hc : charge40 (UnifiedSampler.absorb p n P msg).toBytes T = finalCap n := by
        unfold charge40; rw [hf]
      rw [h]
      rw [hc]
      exact ite_le _ _ hrc hrc0

/-- Weighted per-row bound on the 40-row protocol's chains. -/
theorem row_weight40 (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (n : Nat) (hn : n < 40) (T : Table Bytes State) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T
      (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1 ≤ rowCharge40 n := by
  change decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T
    (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1 ≤ _
  rw [LiteralByteSampler.eval_eq]
  exact sampler_weight40 (fun a => H a.toBytes) n hn _ _ T

theorem rows_weight40 (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (ns : List Nat) (hns : ∀ n ∈ ns, n < 40) (T : Table Bytes State) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T
      (ns.map (fun n =>
        (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1)).flatten ≤
        (ns.map rowCharge40).sum := by
  induction ns generalizing T with
  | nil => simp [decoderFirstWeight]
  | cons n ns ih =>
    rw [List.map_cons, List.flatten_cons, decoderFirstWeight_append, List.map_cons, List.sum_cons]
    have hb := row_weight40 D H pub pf n (hns n (List.mem_cons_self ..)) T
    have ht := ih (fun k hk => hns k (List.mem_cons_of_mem n hk))
      (applyTrace T (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1)
    linarith

/-- The verifier's weighted charge for 40 rows. -/
def verifierCharge40 : ℚ := ((List.range 40).map rowCharge40).sum

/-- Piece (c), verifier part, 40 rows. -/
theorem verifier_weight40 (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 T
      (eval H (AspisRows40.Starts.verifier D d pub pf)).1 ≤ verifierCharge40 := by
  unfold AspisRows40.Starts.verifier
  rw [FS2.verifier_eval]
  exact rows_weight40 D H pub pf (List.range 40) (fun n hn => List.mem_range.mp hn) T

theorem rowCharge40_33 : rowCharge40 33 = capLambda := by
  unfold rowCharge40 finalCap
  rw [if_neg (by omega), if_pos rfl]

theorem rowCharge40_round (n : Nat) (h : 33 < n) : rowCharge40 n = capRound := by
  unfold rowCharge40 finalCap
  rw [if_neg (by omega), if_neg (by omega)]

/-- Closed form: R1's 33-row verifier charge plus `capLambda` and six `capRound`. -/
theorem verifierCharge40_eq :
    verifierCharge40 = verifierCharge + capLambda + 6 * capRound := by
  unfold verifierCharge40 verifierCharge
  rw [show (40 : Nat) = 33 + 7 from rfl, List.range_add, List.map_append, List.sum_append]
  have h1 : (List.range 33).map rowCharge40 = (List.range 33).map rowCharge := by
    apply List.map_congr_left
    intro n hn
    unfold rowCharge40
    rw [if_pos (List.mem_range.mp hn)]
  have h7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  rw [h1, h7]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  rw [rowCharge40_33, rowCharge40_round 34 (by omega), rowCharge40_round 35 (by omega),
    rowCharge40_round 36 (by omega), rowCharge40_round 37 (by omega),
    rowCharge40_round 38 (by omega), rowCharge40_round 39 (by omega)]
  ring

#print axioms charge40_le_capMax
#print axioms sampler_weight40
#print axioms verifier_weight40
#print axioms verifierCharge40_eq
end AspisRowStarts40
end
