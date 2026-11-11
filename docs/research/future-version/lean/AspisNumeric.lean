import AspisRowStarts40
import BinCombinedMerkleCollision
import R0C.SlackBits
import R0C.SlackObstruction

/-! Numeric values of the right-hand side of the Aspis failure bound
(`AspisFailureBound.Joined.failure_bound40P_of_final`).

Kind of result: pure rational arithmetic on the definitions of `capMax`,
`verifierCharge40` and `kappa`. No protocol reasoning. The bound these numbers
enter is conditional on `FinalDecoding40`; nothing here removes that
condition, and nothing here is about deployed code.

Method. The constants (`capMax`, `verifierCharge40`) are reduced to closed
forms by explicit row lemmas and then compared with rationals by `norm_num`.
The query-dependent statement `rhs_per_query` is proved symbolically in a
rational variable `x` (`per_query_core`); no term depending on `Q` is
evaluated. -/
set_option autoImplicit false
noncomputable section
namespace AspisNumeric
open AspisR1 AspisCharge40 AspisRowStarts40 AspisPerStep.RowStarts AspisPerStep.RowCharge

/-- The right-hand side of `failure_bound40P_of_final`, syntactically the same term. -/
abbrev rhs (Q : Nat) : ℚ :=
  BinCombinedMerkleCollision.kappa (Q+1111) +
    ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454

/-! ## Closed forms of the class caps -/

theorem atom_eq :
    SemanticBudget.atom = 1 / (2147483647 : ℚ)^4 + 1 / (2:ℚ)^256 := by
  unfold SemanticBudget.atom R0P.SemSource.deltaQ
  norm_num [AspisCircleGroupOrder.P]

theorem queryCap_eq : UnifiedQueryDensity.queryCap =
    (3204816658150512709790016143025871214703406297554365823658832464480 : ℚ) /
      143459390671643080338858006328548634467103740668941284234642666778199466504034122047364474303283200 := by
  unfold UnifiedQueryDensity.queryCap
  rw [R0C.SlackBits.bad_query_count, R0C.SlackObstruction.query_count]
  norm_num

theorem openingCap_nonneg : 0 ≤ OpeningSamplerBound.openingCap := by
  unfold OpeningSamplerBound.openingCap OpeningSamplerBound.gammaAtom OpeningSamplerBound.atom
  positivity

theorem budget0_eq : LiteralClassifier.budget 0 = 217600 * SemanticBudget.atom := by
  simp only [LiteralClassifier.budget, if_pos (show (0 : Nat) < 25 by omega)]
  rw [SemanticBudget.budget_eq ⟨0, by omega⟩]
  norm_num [SemanticBudget.roots]

theorem budget1_eq : LiteralClassifier.budget 1 = 54400 * SemanticBudget.atom := by
  simp only [LiteralClassifier.budget, if_pos (show (1 : Nat) < 25 by omega)]
  rw [SemanticBudget.budget_eq ⟨1, by omega⟩]
  norm_num [SemanticBudget.roots]

theorem budget26_eq : LiteralClassifier.budget 26 = SemanticBudget.atom := by
  simp only [LiteralClassifier.budget, show ¬ ((26 : Nat) < 25) by omega, if_false]
  rfl

theorem budget31_eq : LiteralClassifier.budget 31 = UnifiedQueryDensity.queryCap := by
  simp only [LiteralClassifier.budget, show ¬ ((31 : Nat) < 25) by omega, if_false]
  try rfl

theorem budget32_eq : LiteralClassifier.budget 32 =
    21 * 5444517880876220229045745149051146347265 / (2^256 : ℚ) := by
  have h : LiteralClassifier.budget 32 = RhoSamplerBound.rhoCap := by
    simp only [LiteralClassifier.budget, show ¬ ((32 : Nat) < 25) by omega, if_false]
    try rfl
  rw [h, ← AspisRowDensity.QM31.capPair_eq_rhoCap, AspisRowDensity.QM31.capPair_eq]

/-! ## Item 1: `capMax` -/

theorem capMax_eq : capMax = UnifiedQueryDensity.queryCap := by
  have hq : (9061 : ℚ) / (10000 * 2^105) ≤ UnifiedQueryDensity.queryCap := by
    rw [queryCap_eq]; norm_num
  apply le_antisymm
  · unfold capMax
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
    · rw [budget0_eq, atom_eq]; refine le_trans ?_ hq; norm_num
    · rw [budget1_eq, atom_eq]; refine le_trans ?_ hq; norm_num
    · rw [budget26_eq, atom_eq]; refine le_trans ?_ hq; norm_num
    · refine le_trans OpeningSamplerBound.openingCap_lt_two_neg_199.le (le_trans ?_ hq)
      norm_num
    · rw [budget31_eq]
    · rw [budget32_eq]; refine le_trans ?_ hq; norm_num
  · unfold capMax
    rw [← budget31_eq]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))

theorem capMax_le_tight : capMax ≤ 9063 / (10000 * 2^105) := by
  rw [capMax_eq, queryCap_eq]; norm_num

theorem capMax_ge : (9061 : ℚ) / (10000 * 2^105) ≤ capMax := by
  rw [capMax_eq, queryCap_eq]; norm_num

theorem capMax_le : capMax ≤ 1 / 2^105 :=
  capMax_le_tight.trans (by norm_num)

/-! ## Item 2: `verifierCharge40` -/

private theorem cc_sem (k : Nat) (h0 : 0 < k) (h : k < 26) :
    classCap k = LiteralClassifier.budget 1 := by
  unfold classCap; rw [if_pos (cls_sem k h0 h)]

private theorem cc_open (k : Nat) (hlo : 27 ≤ k) (hhi : k < 31) :
    classCap k = OpeningSamplerBound.openingCap := by
  unfold classCap
  rw [cls_open k hlo hhi, if_neg (by omega), if_pos rfl]

private theorem cc_one (k : Nat) (hc : cls k = k) (h1 : k ≠ 1) (h27 : k ≠ 27) (h33 : k ≠ 33) :
    classCap k = LiteralClassifier.budget k := by
  unfold classCap
  rw [hc, if_neg h1, if_neg h27, if_neg h33]

/-- The sum of a function over `List.range 33`, written out (no `Q`, no numerals evaluated). -/
theorem sum_range33 (f : Nat → ℚ) : ((List.range 33).map f).sum =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 +
      f 14 + f 15 + f 16 + f 17 + f 18 + f 19 + f 20 + f 21 + f 22 + f 23 + f 24 + f 25 +
      f 26 + f 27 + f 28 + f 29 + f 30 + f 31 + f 32 := by
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  ring

theorem classCaps_sum : ((List.range 33).map classCap).sum =
    LiteralClassifier.budget 0 + 25 * LiteralClassifier.budget 1 +
      LiteralClassifier.budget 26 + 4 * OpeningSamplerBound.openingCap +
      LiteralClassifier.budget 31 + LiteralClassifier.budget 32 := by
  rw [sum_range33 classCap]
  rw [cc_one 0 rfl (by omega) (by omega) (by omega), cc_one 26 rfl (by omega) (by omega) (by omega),
    cc_one 31 rfl (by omega) (by omega) (by omega), cc_one 32 rfl (by omega) (by omega) (by omega)]
  simp (disch := omega) only [cc_sem, cc_open]
  -- the caps are opaque atoms for `ring`
  generalize LiteralClassifier.budget 0 = a0
  generalize LiteralClassifier.budget 1 = a1
  generalize LiteralClassifier.budget 26 = a26
  generalize LiteralClassifier.budget 31 = a31
  generalize LiteralClassifier.budget 32 = a32
  generalize OpeningSamplerBound.openingCap = oc
  ring

/-- Closed form of the 40-row verifier charge. -/
theorem verifierCharge40_closed : verifierCharge40 =
    1577601 * SemanticBudget.atom + 4 * OpeningSamplerBound.openingCap +
      2 * UnifiedQueryDensity.queryCap +
      34 * (5444517880876220229045745149051146347265 / (2^256 : ℚ)) := by
  rw [AspisRowStarts40.verifierCharge40_eq, AspisPerStep.RowStarts.verifierCharge_eq,
    classCaps_sum, budget0_eq, budget1_eq, budget26_eq, budget31_eq, budget32_eq, capMax_eq,
    AspisRowDensity.QM31.capLambda_eq, AspisRowDensity.QM31.capRound_eq]
  ring

theorem verifierCharge40_le_tight : verifierCharge40 ≤ 15068 / (100000 * 2^100) := by
  have ho := OpeningSamplerBound.openingCap_lt_two_neg_199
  rw [verifierCharge40_closed, atom_eq, queryCap_eq]
  norm_num at ho ⊢
  linarith

theorem verifierCharge40_le : verifierCharge40 ≤ 151 / (1000 * 2^100) :=
  verifierCharge40_le_tight.trans (by norm_num)

theorem verifierCharge40_ge : 150 / (1000 * 2^100) ≤ verifierCharge40 := by
  have ho := openingCap_nonneg
  rw [verifierCharge40_closed, atom_eq, queryCap_eq]
  norm_num at ho ⊢
  linarith

/-! ## Item 3: the right-hand side at `Q = 0` -/

/-- `2^454` is above the evaluation threshold, so the scan term is kept as an
atom and bounded by monotonicity. -/
theorem scan_le : 1 / (2:ℚ)^454 ≤ 1 / (2:ℚ)^126 :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem rhs_zero_lt : rhs 0 < 151 / (1000 * 2^100) := by
  have hv := verifierCharge40_le_tight
  have ht := scan_le
  have hk : BinCombinedMerkleCollision.kappa (0 + 1111) = 7405926 / (2:ℚ)^256 := by
    unfold BinCombinedMerkleCollision.kappa; norm_num
  have hz : ((0 : Nat) : ℚ) * capMax = 0 := by simp
  unfold rhs
  rw [hk, hz]
  generalize 1 / (2:ℚ)^454 = T at ht ⊢
  norm_num at hv ht ⊢
  linarith

/-! ## Item 4: the per-query form, symbolically in `x = Q` -/

theorem per_query_core (x c v : ℚ) (hx0 : 0 ≤ x) (hx : x ≤ 2^150)
    (hc : c ≤ 1 / 2^105) (hv : v ≤ 151 / (1000 * 2^100)) :
    6 * (x + 1111)^2 / (256^32 : ℚ) + (x * c + v) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 ≤
      (x + 1) / 2^100 := by
  have hxx : x * x ≤ 2^150 * x := mul_le_mul_of_nonneg_right hx hx0
  have hxc : x * c ≤ x * (1 / 2^105) := mul_le_mul_of_nonneg_left hc hx0
  have e1 : 6 * (x + 1111)^2 / (256^32 : ℚ) =
      6 * (x * x) / 2^256 + 13332 * x / 2^256 + 7405926 / 2^256 := by ring
  have e2 : 6 * (x * x) / (2:ℚ)^256 ≤ 6 * (2^150 * x) / 2^256 := by
    have : (0 : ℚ) < 2^256 := by positivity
    rw [div_le_div_iff_of_pos_right this]
    linarith
  have e3 : 6 * (2^150 * x) / (2:ℚ)^256 = x * (6 / 2^106) := by ring
  have ht := scan_le
  rw [e1]
  generalize 1 / (2:ℚ)^454 = T at ht ⊢
  linarith

theorem rhs_per_query (Q : Nat) (hQ : Q ≤ 2^150) : rhs Q ≤ ((Q : ℚ) + 1) / 2^100 := by
  have hx : (Q : ℚ) ≤ 2^150 := by exact_mod_cast hQ
  unfold rhs BinCombinedMerkleCollision.kappa
  rw [show ((Q + 1111 : Nat) : ℚ) = (Q : ℚ) + 1111 by push_cast; ring]
  exact per_query_core (Q : ℚ) capMax verifierCharge40 (Nat.cast_nonneg Q) hx
    capMax_le verifierCharge40_le

#print axioms atom_eq
#print axioms queryCap_eq
#print axioms openingCap_nonneg
#print axioms budget0_eq
#print axioms budget1_eq
#print axioms budget26_eq
#print axioms budget31_eq
#print axioms budget32_eq
#print axioms capMax_eq
#print axioms capMax_le_tight
#print axioms capMax_ge
#print axioms capMax_le
#print axioms sum_range33
#print axioms classCaps_sum
#print axioms verifierCharge40_closed
#print axioms verifierCharge40_le_tight
#print axioms verifierCharge40_le
#print axioms verifierCharge40_ge
#print axioms scan_le
#print axioms rhs_zero_lt
#print axioms per_query_core
#print axioms rhs_per_query
end AspisNumeric
end
