import AspisRowCharge
import AspisWeightedFirstRead
import BinHonestQueryBudget

/-! Per-step accounting, piece (c), verifier part: the weighted count of the
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

/-! ## Caps: nonnegativity and the largest cap -/

private theorem atom_nonneg : 0 ≤ SemanticBudget.atom := by
  unfold SemanticBudget.atom R0P.SemSource.deltaQ
  positivity

private theorem sem_budget_nonneg (i : Nat) (h : i < 25) : 0 ≤ LiteralClassifier.budget i := by
  simp only [LiteralClassifier.budget, if_pos h]
  rw [SemanticBudget.budget_eq ⟨i, h⟩]
  exact mul_nonneg (Nat.cast_nonneg _) atom_nonneg

private theorem budget26_nonneg : 0 ≤ LiteralClassifier.budget 26 := by
  have he : LiteralClassifier.budget 26 = SemanticBudget.atom := by
    simp only [LiteralClassifier.budget, show ¬ ((26 : Nat) < 25) by omega, if_false]
    rfl
  rw [he]; exact atom_nonneg

private theorem budget31_nonneg : 0 ≤ LiteralClassifier.budget 31 := by
  simp only [LiteralClassifier.budget, show ¬ ((31 : Nat) < 25) by omega, if_false]
  unfold UnifiedQueryDensity.queryCap
  positivity

private theorem budget32_nonneg : 0 ≤ LiteralClassifier.budget 32 := by
  simp only [LiteralClassifier.budget, show ¬ ((32 : Nat) < 25) by omega, if_false]
  unfold RhoSamplerBound.rhoCap
  positivity

private theorem openingCap_nonneg : 0 ≤ OpeningSamplerBound.openingCap := by
  have hg := LiteralOpeningDensity.gammaBudget_nonneg
  have hk := LiteralOpeningDensity.kappaBudget_nonneg
  have hf := LiteralOpeningDensity.foldBudget_nonneg
  have he : OpeningSamplerBound.openingCap = LiteralOpeningDensity.gammaBudget +
      LiteralOpeningDensity.kappaBudget + 2 * LiteralOpeningDensity.foldBudget := by
    unfold OpeningSamplerBound.openingCap LiteralOpeningDensity.gammaBudget
      LiteralOpeningDensity.kappaBudget LiteralOpeningDensity.foldBudget
    ring
  rw [he]; linarith

theorem cls_cases (n : Nat) :
    cls n = 0 ∨ cls n = 1 ∨ cls n = 26 ∨ cls n = 27 ∨ cls n = 31 ∨ cls n = 32 ∨ cls n = 33 := by
  unfold cls
  split_ifs <;> simp

/-- The largest class cap (a symbolic maximum; its value is computed in the note). -/
def capMax : ℚ :=
  max (LiteralClassifier.budget 0) (max (LiteralClassifier.budget 1)
    (max (LiteralClassifier.budget 26) (max OpeningSamplerBound.openingCap
      (max (LiteralClassifier.budget 31) (LiteralClassifier.budget 32)))))

theorem capMax_nonneg : 0 ≤ capMax :=
  (sem_budget_nonneg 0 (by omega)).trans (le_max_left _ _)

theorem classCap_nonneg (n : Nat) : 0 ≤ classCap n := by
  unfold classCap
  split_ifs with h1 h27 h33
  · exact sem_budget_nonneg 1 (by omega)
  · exact openingCap_nonneg
  · exact le_refl 0
  · rcases cls_cases n with h | h | h | h | h | h | h
    · rw [h]; exact sem_budget_nonneg 0 (by omega)
    · exact absurd h h1
    · rw [h]; exact budget26_nonneg
    · exact absurd h h27
    · rw [h]; exact budget31_nonneg
    · rw [h]; exact budget32_nonneg
    · exact absurd h h33

theorem classCap_le_capMax (n : Nat) : classCap n ≤ capMax := by
  unfold classCap capMax
  split_ifs with h1 h27 h33
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact capMax_nonneg
  · rcases cls_cases n with h | h | h | h | h | h | h
    · rw [h]; exact le_max_left _ _
    · exact absurd h h1
    · rw [h]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    · exact absurd h h27
    · rw [h]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
    · rw [h]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))
    · exact absurd h h33

/-- The charge used for R1's decoder. -/
abbrev wt : Bytes → Table Bytes State → ℚ := charge RawFullPublicSelection.select

theorem wt_nonneg (a : Bytes) (T : Table Bytes State) : 0 ≤ wt a T := by
  unfold wt charge
  split
  · exact classCap_nonneg _
  · exact le_refl 0

theorem wt_le_capMax (a : Bytes) (T : Table Bytes State) : wt a T ≤ capMax := by
  unfold wt charge
  split
  · exact classCap_le_capMax _
  · exact capMax_nonneg

/-! ## The charge of the frames the sampler reads -/

private theorem classCap_33 : classCap 33 = 0 := by
  have hc : cls 33 = 33 := by unfold cls; simp
  unfold classCap; rw [hc, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- The absorb frame of row `n` decodes, if at all, to component `n`. -/
theorem wt_absorb (s : State) (n : Nat) (hn : n < 33) (data : Bytes) (hd : data.length ≤ p.D)
    (T : Table Bytes State) :
    wt (absorbA p s (p.lbl n) data hd).toBytes T ≤ classCap n := by
  unfold wt charge
  cases hs : RawFullPublicSelection.select (absorbA p s (p.lbl n) data hd).toBytes T with
  | none => exact classCap_nonneg n
  | some pub =>
    have hc : CanonicalByteAddress.Canonical (absorbA p s (p.lbl n) data hd) :=
      CanonicalByteAddress.canonical_ofBytes _ _
    have hdec : CanonicalRawTrace.decode L (absorbA p s (p.lbl n) data hd).toBytes =
        some ⟨_, hc⟩ := by
      have h := (CanonicalRawTrace.embedding L).decode_embed (⟨_, hc⟩ : AddrC L)
      change CanonicalRawTrace.decode L (toBytes (⟨_, hc⟩ : AddrC L)) = some ⟨_, hc⟩ at h
      exact h
    have hrow : rawRow pub (absorbA p s (p.lbl n) data hd).toBytes = n := by
      unfold rawRow
      rw [hdec]
      dsimp only
      unfold rowOf
      rw [PublicInitAbsorbSeparation.parse_init_absorb_none p pub.pubBytes s (p.lbl n) data hd]
      simp only [Option.isSome_none, Bool.false_eq_true, if_false, parseAbsorb_absorbA]
      exact UnifiedLabels.row_label n hn
    simp only [hrow, le_refl]

/-- The initialization frame decodes, if at all, to component 0. -/
theorem wt_init (pubBytes : Bytes) (hL : 75 + pubBytes.length ≤ L) (c1 : State)
    (T : Table Bytes State) :
    wt (PublicInitFrame.addr pubBytes hL c1).toBytes T ≤ classCap 0 := by
  unfold wt charge
  cases hs : RawFullPublicSelection.select (PublicInitFrame.addr pubBytes hL c1).toBytes T with
  | none => exact classCap_nonneg 0
  | some pub =>
    have hc : CanonicalByteAddress.Canonical (PublicInitFrame.addr pubBytes hL c1) :=
      CanonicalByteAddress.canonical_ofBytes _ _
    have hdec : CanonicalRawTrace.decode L (PublicInitFrame.addr pubBytes hL c1).toBytes =
        some ⟨_, hc⟩ := by
      have h := (CanonicalRawTrace.embedding L).decode_embed (⟨_, hc⟩ : AddrC L)
      change CanonicalRawTrace.decode L (toBytes (⟨_, hc⟩ : AddrC L)) = some ⟨_, hc⟩ at h
      exact h
    have hnone : parseAbsorb (PublicInitFrame.addr pubBytes hL c1) = none := by
      have htag : (PublicInitFrame.addr pubBytes hL c1).toBytes.getD 32 (1 : AspisV8R19.DuplexFrames.Byte) = 84 := by
        rw [PublicInitFrame.addr_bytes]
        simp [PublicInitFrame.domain, PublicInitFrame.lengthBytes]
      have hfalse : ¬ (34 ≤ (PublicInitFrame.addr pubBytes hL c1).toBytes.length ∧
          (PublicInitFrame.addr pubBytes hL c1).toBytes.getD 32 (1 : AspisV8R19.DuplexFrames.Byte) = 0) := by
        intro hcond
        have hbad := hcond.2
        rw [htag] at hbad
        exact (by decide : (84 : AspisV8R19.DuplexFrames.Byte) ≠ 0) hbad
      unfold parseAbsorb
      exact if_neg hfalse
    simp only []
    unfold rawRow
    rw [hdec]
    dsimp only
    unfold rowOf
    split_ifs
    · exact le_refl _
    · rw [hnone]
      dsimp only
      rw [classCap_33]
      exact classCap_nonneg 0

/-! ## One sampler row -/

/-- Weighted charge of R1's sampler row `n`. -/
def rowCharge (n : Nat) : ℚ := classCap n + (if n = 26 then capMax else 0)

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

/-- The verifier's weighted charge: the sum of the 33 row charges. -/
def verifierCharge : ℚ := ((List.range 33).map rowCharge).sum

/-- Piece (c), verifier part (weighted analogue of `BinHonestQueryBudget.verifier_starts`). -/
theorem verifier_weight (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstWeight dec wt T (eval H (verifier D d pub pf)).1 ≤ verifierCharge := by
  unfold RawCutProverCompiler.verifier
  rw [FS2.verifier_eval]
  exact rows_weight D H pub pf (List.range 33) (fun n hn => List.mem_range.mp hn) T

private theorem sum_indicator26 (c : ℚ) : ∀ N : Nat,
    ((List.range N).map (fun n => if n = 26 then c else 0)).sum = if 26 < N then c else 0
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_indicator26 c N]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> first | (exfalso; omega) | ring

/-- The verifier charge in closed form: the sum of the 33 class caps plus one
largest cap for the row-26 reseed frame. -/
theorem verifierCharge_eq :
    verifierCharge = ((List.range 33).map classCap).sum + capMax := by
  unfold verifierCharge rowCharge
  rw [List.sum_map_add, sum_indicator26 capMax 33, if_pos (by omega)]

#print axioms wt_absorb
#print axioms wt_init
#print axioms sampler_weight
#print axioms rows_weight
#print axioms verifier_weight
#print axioms verifierCharge_eq
end AspisPerStep.RowStarts
end
