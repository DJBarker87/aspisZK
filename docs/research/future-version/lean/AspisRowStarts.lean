import AspisRowCharge
import AspisWeightedFirstRead
import AspisHonestBudgetBase
import AspisLib_Recorded

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
open BinHonestStartFrames AspisHonestBudgetBase
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

/-- The verifier's weighted charge: the sum of the 33 row charges. -/
def verifierCharge : ℚ := ((List.range 33).map rowCharge).sum

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
#print axioms verifierCharge_eq
end AspisPerStep.RowStarts
end
