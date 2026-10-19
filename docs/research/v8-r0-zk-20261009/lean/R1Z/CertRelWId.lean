import R1Z.CertRelK
import R1Z.CertRelIdent
import R1Z.RfOwn
import AspisFormal.CircleNaturalBasisEval

/-! D64 hRel (2b), pure part (no Aeneas): the CertRelK models are the Lean objects, for
abstract input functions under named premises — alpha `A`, OOD limbs `Z`, transport
`T = π`, inverse transport `TI = π⁻¹`, inactive flags `Fl`, openings `κ, α₀, α₁`:

* `ellP_single0..6`: `ellP` at row `π⁻¹ j` is `ell π ch k (e_j)`;
* `wtP_ident`, `w1P_ident`, `w2P_ident`: `wtP = weightsR1`, `w1P = w1`, `w2P = w2`;
* `lfvP_eq`: `lfvP` (half `1/2`) is `lineFoldValue` of the unit vector;
* `natP_eq`: the bit-by-bit natural basis is `naturalLineValue` (CertNatural, restated
  for `natP`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRel

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R1Z.Batched R1Z.RfOwn AspisCircleTensorBinding

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-! ### Closed forms (CertLiftIdent part A, for the P models) -/

theorem scP_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩) :
    ∀ n, n ≤ 10 → scP A n = succCarry α n
  | 0, _ => by simp [scP, succCarry]
  | n + 1, hn => by
      rw [scP, Finset.prod_range_succ, ← scP, scP_eq α A hA n (by omega), succCarry, dif_pos (by omega),
        hA _ (by omega), mul_comm]

theorem pcP_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (g c : ℕ) (hg : g < 3) (hc : c < 10) : pcP A g c = rustPoints α ⟨g, hg⟩ ⟨c, hc⟩ := by
  unfold pcP
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
  · simp [rustPoints, hA c hc]
  · simp only [rustPoints, successorPoint, if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true]
    rw [scP_eq α A hA _ (by omega), hA c hc]
  · simp only [rustPoints, xor12Point, if_neg (show (2 : ℕ) ≠ 0 by norm_num),
      if_neg (show (2 : ℕ) ≠ 1 by norm_num), hA c hc]

theorem eqP_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (g : ℕ) (hg : g < 3) (r : Fin 1024) : eqP A g r.val = rustEq (rustPoints α ⟨g, hg⟩) r := by
  unfold eqP rustEq
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pcP_eq α A hA g i hg i.2]
  rcases Nat.mod_two_eq_zero_or_one (r.val / 2 ^ (9 - i.val)) with h | h
  · rw [h, if_neg (by omega)]; simp
  · rw [h, if_pos rfl]; push_cast; ring

theorem hwP_eq (α : Fin 10 → K) (A : ℕ → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = α ⟨j, h⟩)
    (co : Fin 1024) : hwP A co.val = rustHWeight α co := by
  unfold hwP rustHWeight
  rw [hA 8 (by norm_num), hA 9 (by norm_num)]
  rfl

theorem df_succP (x : K) : ∀ b : ℕ, doubledFactor x (b + 1) = doubledFactor (x * x + x * x - 1) b
  | 0 => by simp [doubledFactor]; ring
  | b + 1 => by rw [doubledFactor, df_succP x b, doubledFactor]

theorem nlv_evenP (x : K) (n : ℕ) :
    naturalLineValue x (2 * n) = naturalLineValue (x * x + x * x - 1) n := by
  unfold naturalLineValue
  rw [List.prod_toFinset _ Nat.bitIndices_nodup, List.prod_toFinset _ Nat.bitIndices_nodup,
    Nat.bitIndices_two_mul, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => df_succP x b

theorem nlv_oddP (x : K) (n : ℕ) :
    naturalLineValue x (2 * n + 1) = x * naturalLineValue (x * x + x * x - 1) n := by
  unfold naturalLineValue
  rw [List.prod_toFinset _ Nat.bitIndices_nodup, List.prod_toFinset _ Nat.bitIndices_nodup,
    Nat.bitIndices_two_mul_add_one, List.map_cons, List.prod_cons, List.map_map]
  congr 1
  congr 1
  exact List.map_congr_left fun b _ => df_succP x b

theorem natP_eq (x : K) : ∀ (k m : ℕ), m < 2 ^ k → natP x m k = naturalLineValue x m
  | 0, m, hm => by
      have : m = 0 := by simpa using hm
      subst this
      simp [natP, naturalLineValue]
  | k + 1, m, hm => by
      rw [natP, natP_eq (x * x + x * x - 1) k (m / 2) (by rw [pow_succ] at hm; omega)]
      rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
      · have hm2 : m = 2 * (m / 2) := by omega
        rw [h0, Nat.cast_zero, zero_mul, add_zero, one_mul]
        conv_rhs => rw [hm2]
        rw [nlv_evenP]
      · have hm2 : m = 2 * (m / 2) + 1 := by omega
        rw [h1, Nat.cast_one, one_mul, add_sub_cancel]
        conv_rhs => rw [hm2]
        rw [nlv_oddP]

theorem evP_eq (X Y : K) (co : Fin 1024) : evP X Y co.val = rustEvalRow co X Y := by
  unfold evP rustEvalRow
  rw [natP_eq X 10 (co.val / 2) (by have := co.2; norm_num; omega)]

theorem dot_single {n : ℕ} (v : Fin n → K) (j : Fin n) : dotLinear v (Pi.single j 1) = v j := by
  rw [dotLinear_apply]
  simp [Pi.single_apply]

/-! ### The seven functionals at row `π⁻¹ j` -/

variable (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (A Z : ℕ → K) (T TI : ℕ → ℕ) (Fl : ℕ → K)
  (hA : ∀ (j : ℕ) (h : j < 10), A j = alpha ch ⟨j, h⟩)
  (hZx : ∀ j : Fin 2, Z (2 * j.val) = (ch.circle j).1.1)
  (hZy : ∀ j : Fin 2, Z (2 * j.val + 1) = (ch.circle j).1.2)
  (hT : ∀ r : Fin 1024, T r.val = (π r).val)
  (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
  (hTI : ∀ j : Fin 1024, TI j.val = (π.symm j).val)

include hFl hTI in
theorem ellP_single0 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 0 = ell π ch 0 (Pi.single j 1) := by
  rw [hTI j]
  unfold ellP
  rw [if_pos rfl, hFl (π.symm j), ell_zero, dot_single, AspisR0.Opening.indicator]
  all_goals (by_cases hm : π.symm j ∈ copyInactiveRows <;> simp [hm])

include hA hTI in
theorem ellP_single1 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 1 = ell π ch 1 (Pi.single j 1) := by
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_pos (show (1 : ℕ) - 1 < 3 by norm_num),
    eqP_eq (alpha ch) A hA (1 - 1) (by norm_num) (π.symm j), ell_one, dot_single]
  rw [openingPoints_eq, ← rustEq_eq]
  rfl

include hA hTI in
theorem ellP_single2 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 2 = ell π ch 2 (Pi.single j 1) := by
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_pos (show (2 : ℕ) - 1 < 3 by norm_num),
    eqP_eq (alpha ch) A hA (2 - 1) (by norm_num) (π.symm j), ell_two, dot_single]
  rw [openingPoints_eq, ← rustEq_eq]
  rfl

include hA hTI in
theorem ellP_single3 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 3 = ell π ch 3 (Pi.single j 1) := by
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_pos (show (3 : ℕ) - 1 < 3 by norm_num),
    eqP_eq (alpha ch) A hA (3 - 1) (by norm_num) (π.symm j), ell_three, dot_single]
  rw [openingPoints_eq, ← rustEq_eq]
  rfl

include hA hT hTI in
theorem ellP_single4 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 4 = ell π ch 4 (Pi.single j 1) := by
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_neg (show ¬ ((4 : ℕ) - 1 < 3) by norm_num), if_pos (show (4 : ℕ) - 1 = 3 by norm_num),
    hT (π.symm j), Equiv.apply_symm_apply, hwP_eq (alpha ch) A hA j, rustHWeight_eq, ell_four, dot_single]

include hZx hZy hT hTI in
theorem ellP_single5 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 5 = ell π ch 5 (Pi.single j 1) := by
  have hu : (Pi.single j (1 : K) : Fin 1024 → K) = unitMsg j := by
    funext i
    simp [Pi.single_apply, unitMsg]
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_neg (show ¬ ((5 : ℕ) - 1 < 3) by norm_num), if_neg (show ¬ ((5 : ℕ) - 1 = 3) by norm_num),
    show 2 * ((5 : ℕ) - 1 - 4) = 2 * (0 : Fin 2).val from rfl, hZx 0, hZy 0, hT (π.symm j), Equiv.apply_symm_apply,
    evP_eq, ell_five, hu, oodLinear_unit]

include hZx hZy hT hTI in
theorem ellP_single6 (j : Fin 1024) : ellP A Z T Fl (TI j.val) 6 = ell π ch 6 (Pi.single j 1) := by
  have hu : (Pi.single j (1 : K) : Fin 1024 → K) = unitMsg j := by
    funext i
    simp [Pi.single_apply, unitMsg]
  rw [hTI j]
  unfold ellP headP
  rw [if_neg (by norm_num), if_neg (show ¬ ((6 : ℕ) - 1 < 3) by norm_num), if_neg (show ¬ ((6 : ℕ) - 1 = 3) by norm_num),
    show 2 * ((6 : ℕ) - 1 - 4) = 2 * (1 : Fin 2).val from rfl, hZx 1, hZy 1, hT (π.symm j), Equiv.apply_symm_apply,
    evP_eq, ell_six, hu, oodLinear_unit]

/-! ### Weights and dual folds -/

include hA hZx hZy hT hFl hTI in
theorem wtP_ident (κ : K) (hκ : κ = ch.opening 1) (j : Fin 1024) :
    wtP A Z T TI Fl κ j.val = weightsR1 π ch j := by
  have hw : weightsR1 π ch j = ∑ k : Fin 7, ch.opening 1 ^ k.val * ell π ch k (Pi.single j 1) := by
    rw [← dot_weightsR1 π ch (Pi.single j 1)]
    simp [AspisR1.RoundPairing.dot, Pi.single_apply]
  have e0 : ((0 : Fin 7) : ℕ) = 0 := rfl
  have e1 : ((1 : Fin 7) : ℕ) = 1 := rfl
  have e2 : ((2 : Fin 7) : ℕ) = 2 := rfl
  have e3 : ((3 : Fin 7) : ℕ) = 3 := rfl
  have e4 : ((4 : Fin 7) : ℕ) = 4 := rfl
  have e5 : ((5 : Fin 7) : ℕ) = 5 := rfl
  have e6 : ((6 : Fin 7) : ℕ) = 6 := rfl
  unfold wtP
  rw [hw, Fin.sum_univ_seven]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, e4, e5, e6]
  rw [ellP_single0 π ch A Z T TI Fl hFl hTI j, ellP_single1 π ch A Z T TI Fl hA hTI j,
    ellP_single2 π ch A Z T TI Fl hA hTI j, ellP_single3 π ch A Z T TI Fl hA hTI j,
    ellP_single4 π ch A Z T TI Fl hA hT hTI j, ellP_single5 π ch A Z T TI Fl hZx hZy hT hTI j,
    ellP_single6 π ch A Z T TI Fl hZx hZy hT hTI j, hκ]

include hA hZx hZy hT hFl hTI in
theorem w1P_ident (κ α0 Q : K) (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2)
    (hQ : Q = AspisR1.RoundPairing.quarter) (d : Fin 256) :
    w1P A Z T TI Fl κ α0 Q d.val = w1 π ch d := by
  unfold w1P w1 AspisR1.RoundPairing.dualFold
  rw [← Fin.sum_univ_eq_sum_range (fun t => wtP A Z T TI Fl κ (4 * d.val + t) * α0 ^ ((4 - t) % 4)) 4, hQ, hα0]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← wtP_ident π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ hκ (AspisR1.childIndex d t)]
  rfl

include hA hZx hZy hT hFl hTI in
theorem w2P_ident (κ α0 α1 Q : K) (hκ : κ = ch.opening 1) (hα0 : α0 = ch.opening 2) (hα1 : α1 = ch.opening 3)
    (hQ : Q = AspisR1.RoundPairing.quarter) (e : Fin 64) :
    w2P A Z T TI Fl κ α0 α1 Q e.val = w2 π ch e := by
  subst hQ
  unfold w2P w2 AspisR1.RoundPairing.dualFold
  rw [← Fin.sum_univ_eq_sum_range (fun t => w1P A Z T TI Fl κ α0 AspisR1.RoundPairing.quarter (4 * e.val + t) *
    α1 ^ ((4 - t) % 4)) 4, hα1]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← w1P_ident π ch A Z T TI Fl hA hZx hZy hT hFl hTI κ α0 _ hκ hα0 rfl (AspisR1.childIndex e t)]
  rfl

/-! ### Line fold, natural basis, M31 constants -/

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem lfvP_eq (H a i0 i1 i2 : K) (hH : H = 1 / 2) (t : ℕ) (ht : t < 4) :
    lfvP H a i0 i1 i2 t = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue a i0 i1 i2
      (fun s => if t = s.val then 1 else 0) := by
  have f0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have f1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have f2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have f3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
    simp only [lfvP, pfP, AspisV5ComponentCConcreteFoldLinearity.lineFoldValue,
      AspisV5ComponentCConcreteFoldLinearity.pairFoldValue, hH, f0, f1, f2, f3] <;> ring

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem e_half (e : ZMod 2147483647 →+* K) : e 1073741824 = 1 / 2 := by
  have h2 : (2 * 1073741824 : ZMod 2147483647) = 1 := rfl
  have : (2 : K) * e 1073741824 = 1 := by
    rw [← map_ofNat e 2, ← map_mul, h2, map_one]
  rw [one_div]
  exact eq_inv_of_mul_eq_one_right this

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
theorem e_quarter (e : ZMod 2147483647 →+* K) : e 536870912 = AspisR1.RoundPairing.quarter := by
  have h4 : (4 * 536870912 : ZMod 2147483647) = 1 := rfl
  have : (4 : K) * e 536870912 = 1 := by
    rw [← map_ofNat e 4, ← map_mul, h4, map_one]
  exact eq_inv_of_mul_eq_one_right this

#print axioms scP_eq
#print axioms eqP_eq
#print axioms natP_eq
#print axioms evP_eq
#print axioms ellP_single0
#print axioms ellP_single1
#print axioms ellP_single4
#print axioms ellP_single5
#print axioms wtP_ident
#print axioms w1P_ident
#print axioms w2P_ident
#print axioms lfvP_eq
#print axioms e_half
#print axioms e_quarter

end R1Z.CertRel

end
