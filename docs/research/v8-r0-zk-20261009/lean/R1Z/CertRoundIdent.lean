import R1Z.CertRoundK
import R1Z.RfOwn
import R1Z.RfChain
import R1Z.CertData
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.FinCases

/-! D59.2 / D62.3 / D64.2 (hRound, hGRound): the pure-round coordinates of the checker's
sources are the Rust `round_row` / `tail_row` model `srcRoundR` (CertRoundK).

* `roundMaskMap_coeff`: a source's round image is the coefficient table of
  `rounds ch j (maskLinear ∘ pureTrace)` (`A_pure`, `L_round`).
* `z4c_poly`: the Z4c coordinates of a family of round polynomials of degree `< 28`
  are `zq` (initial sum `P₀(0) + P₀(1)`, then the stored coefficients).
* `rounds_maskOnlySrc`, `rounds_gSrc`: by `R0Z.PureRounds.pureRound_maskOnly` /
  `pureRound_G` and the balanced word, the round polynomials are `rowPoly` at row `r`
  minus (copy-inactive `r`) `rowPoly` at row 0; `rounds_dSrc`: by `extra_balWord` and
  `coordinate_power_round`, the Libra rounds `tPoly` at `π r` and `π 0`.
* `zq_row`, `zq_tail`: the closed forms equal the Rust loops entry by entry
  (`pcR_eq`, `coeff_bitMul`, `bR_eq`, `prefR_eq`, `boolR_split`, `tcell_eq`).
* `z4c_srcTape`: for every lane `c` (mask-only `c < 10`, G `c = 10`, D otherwise, the
  dispatch of `CertOwn.mkSrc`), row `r ≠ 0` and limb `k`,
  `z4c (roundMaskMap (srcTape c r k)) p = srcRoundR A T Fl B.i B.u c r k p`, under the
  named input premises `hA` (alpha), `hT` (transport `T r = π r`), `hFl` (inactive flags).
* `round_ident`: hence the `hRound`/`hGRound` shape `flat (z4c …) i = φ (colM m s i t)`
  from the entry premise `pack4 (φ ∘ limbs of column t, coordinate p) = srcRoundR …`.

No round matrix, Boolean cube or row table is evaluated. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRound

open scoped BigOperators
open Polynomial
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12
  R0Z.Shift R0Z.Chain R0Z.Z4Maps R0Z.PureRounds
open R1Z.RfSrc

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Sums against the balanced word, in a module -/

theorem sum_smul_balWord {V : Type*} [AddCommGroup V] [Module K V] (f : Fin 1024 → V)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) :
    ∑ s, balWord d r x s • f s = x • f r - (if r ∈ copyInactiveRows then x • f d else 0) := by
  have e : ∀ s, balWord d r x s • f s =
      (if s = r then x • f r else 0) +
        (if s = d then (if r ∈ copyInactiveRows then -(x • f d) else 0) else 0) := by
    intro s
    unfold balWord
    by_cases h1 : s = r
    · have h2 : ¬ s = d := fun h => hr (h1.symm.trans h)
      rw [if_pos h1, if_pos h1, if_neg h2, h1, add_zero]
    · by_cases h2 : s = d
      · rw [if_neg h1, if_neg h1, zero_add, if_pos h2]
        by_cases hm : r ∈ copyInactiveRows
        · rw [if_pos ⟨h2, hm⟩, if_pos hm, h2, neg_smul]
        · rw [if_neg (fun h => hm h.2), if_neg hm, zero_smul]
      · rw [if_neg h1, if_neg h1, if_neg (fun h => h2 h.1), if_neg h2, zero_smul, add_zero]
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> abel

/-! ### Round images as coefficient tables -/

theorem roundMaskMap_coeff {Bat : Type} [BatchedLayer K Bat] (π : Fin 1024 ≃ Fin 1024)
    (B : PackBasis F) (ch : Challenges K) (m : M K F) (j : Fin 10) (i : Fin 28) :
    R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch m j i =
      (R0Z.PayloadSplit.rounds ch j
        (fun a => R0Z.PayloadSplit.maskLinear π B a (pureTrace B m))).coeff i.val := by
  rw [R1Z.RfChain.roundMaskMap_apply, A_pure, R0Z.PayloadSplit.L_round]

theorem pev_coeff (P : K[X]) (hP : P.natDegree < 28) (x : K) :
    R1Z.RfChain.pev (fun i : Fin 28 => P.coeff i.val) x = P.eval x := by
  unfold R1Z.RfChain.pev
  rw [eval_eq_sum_range' hP]
  exact Fin.sum_univ_eq_sum_range (fun i => P.coeff i * x ^ i) 28

/-- The Z4c coordinates of a family of round polynomials. -/
def zq (Q : Fin 10 → K[X]) (p : Fin 271) : K :=
  if p.val = 0 then (Q 0).eval 0 + (Q 0).eval 1
  else (Q ⟨(p.val - 1) / 27, by omega⟩).coeff (R1Z.RfChain.coeffOf ⟨(p.val - 1) % 27, by omega⟩).val

theorem z4c_poly (Q : Fin 10 → K[X]) (hQ : ∀ j, (Q j).natDegree < 28) :
    R1Z.RfChain.z4c (fun j (i : Fin 28) => (Q j).coeff i.val) = zq Q := by
  funext p
  simp only [R1Z.RfChain.z4c, zq]
  split_ifs
  · rw [pev_coeff _ (hQ 0), pev_coeff _ (hQ 0)]
  · rfl

theorem zq_comb (x c : K) (Q Q' : Fin 10 → K[X]) (p : Fin 271) :
    zq (fun j => x • (Q j - c • Q' j)) p = x * (zq Q p - c * zq Q' p) := by
  simp only [zq]
  split_ifs
  · simp only [eval_smul, eval_sub, smul_eq_mul]
    ring
  · simp only [coeff_smul, coeff_sub, smul_eq_mul]

theorem coeffOf_val (k : Fin 27) : (R1Z.RfChain.coeffOf k).val = coeffR k.val := by
  unfold R1Z.RfChain.coeffOf coeffR
  split_ifs <;> rfl

/-! ### The mask-only and G rows -/

/-- Row `s`'s round-`j` polynomial: `τ·eqPrefix·(X or 1-X)·(q + (w_j X + β)^e)`. -/
def rowPoly (τ q : K) (fam e : ℕ) (a : Fin 10 → K) (s : Fin 1024) (j : Fin 10) : K[X] :=
  (τ * eqPrefix a s j) • ((if rowBits s j then X else 1 - X) *
    (C q + (C (R0Z.PureRounds.w fam j) * X + C (β (R0Z.PureRounds.w fam) a j s)) ^ e))

theorem row_coeff (τ q : K) (fam e : ℕ) (a : Fin 10 → K) (s : Fin 1024) (j : Fin 10) (n : ℕ) :
    (rowPoly τ q fam e a s j).coeff n = fullR (rowBits s j)
      (fun d => ((if d = 0 then q else 0) +
        pcR (β (R0Z.PureRounds.w fam) a j s) (R0Z.PureRounds.w fam j) e d) * (τ * eqPrefix a s j)) n := by
  unfold rowPoly
  rw [coeff_smul, smul_eq_mul, coeff_bitMul, mul_comm (τ * eqPrefix a s j), ← fullR_mul]
  apply fullR_congr
  intro d
  simp only [coeff_add, coeff_C, pcR_eq]

theorem eqPrefix_zero (a : Fin 10 → K) (s : Fin 1024) : eqPrefix a s 0 = 1 := by
  unfold eqPrefix
  exact Finset.prod_eq_one (fun i _ => if_neg (Nat.not_lt_zero _))

theorem boolR_split (fam : ℕ) (a : Fin 10 → K) (s : Fin 1024) :
    boolR fam s.val = (if rowBits s 0 then R0Z.PureRounds.w fam 0 else 0) +
      β (R0Z.PureRounds.w fam) a 0 s := by
  have h0 : (∑ i : Fin 10, if i.val < (0 : Fin 10).val then R0Z.PureRounds.w fam i * a i else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => if_neg (Nat.not_lt_zero _))
  have h1 : (∑ i : Fin 10, if (0 : Fin 10).val < i.val then
      R0Z.PureRounds.w fam i * (if rowBits s i then 1 else 0) else 0) =
      ∑ n ∈ Finset.range 10, (if 0 < n then wR fam n * (if bitR s.val n = true then 1 else 0) else (0 : K)) :=
    Fin.sum_univ_eq_sum_range (fun n => if 0 < n then wR fam n * (if bitR s.val n = true then 1 else 0) else (0 : K)) 10
  have ht : ∀ n ∈ Finset.range 10, (if bitR s.val n = true then wR fam n else (0 : K)) =
      (if n = 0 then (if bitR s.val 0 = true then wR fam 0 else (0 : K)) else 0) +
      (if 0 < n then wR fam n * (if bitR s.val n = true then 1 else 0) else 0) := by
    intro n _
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · rw [if_neg (Nat.pos_iff_ne_zero.1 h), if_pos h, zero_add]
      split_ifs <;> simp
  unfold β
  rw [h0, h1, zero_add, boolR, Finset.sum_congr rfl ht, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 (by norm_num))]
  rfl

theorem row_eval (τ q : K) (fam e : ℕ) (a : Fin 10 → K) (s : Fin 1024) :
    (rowPoly τ q fam e a s 0).eval 0 + (rowPoly τ q fam e a s 0).eval 1 =
      τ * (q + boolR fam s.val ^ e) := by
  rw [boolR_split fam a s]
  unfold rowPoly
  rw [eqPrefix_zero]
  by_cases h : rowBits s 0 = true
  · rw [if_pos h, if_pos h]
    simp only [eval_smul, smul_eq_mul, eval_mul, eval_add, eval_C, eval_pow, eval_X, eval_sub, eval_one]
    ring
  · rw [if_neg h, if_neg h]
    simp only [eval_smul, smul_eq_mul, eval_mul, eval_add, eval_C, eval_pow, eval_X, eval_sub, eval_one]
    ring

theorem bR_eq (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (fam : ℕ) (j : Fin 10) (s : Fin 1024) :
    bR A fam j.val s.val = β (R0Z.PureRounds.w fam) a j s := by
  unfold bR β
  congr 1
  · have e : ∀ i : Fin 10, (if i.val < j.val then R0Z.PureRounds.w fam i * a i else 0) =
        (if i.val < j.val then wR fam i.val * A i.val else (0 : K)) := by
      intro i
      rw [hA i.val i.isLt]
      rfl
    symm
    rw [Finset.sum_congr rfl (fun i _ => e i),
      Fin.sum_univ_eq_sum_range (fun n => if n < j.val then wR fam n * A n else (0 : K)) 10,
      ← Finset.sum_range_add_sum_Ico _ (show j.val ≤ 10 by omega),
      Finset.sum_eq_zero (s := Finset.Ico j.val 10)
        (fun n hn => if_neg (by rw [Finset.mem_Ico] at hn; omega)), add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos (Finset.mem_range.1 hn), mul_comm]
  · symm
    refine (Fin.sum_univ_eq_sum_range (fun n => if j.val < n then wR fam n *
      (if bitR s.val n = true then 1 else 0) else (0 : K)) 10).trans ?_
    apply Finset.sum_congr rfl
    intro n _
    by_cases h1 : j.val < n <;> by_cases h2 : bitR s.val n = true <;> simp [h1, h2]

theorem prefR_eq (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (j : Fin 10) (s : Fin 1024) : prefR A j.val s.val = eqPrefix a s j := by
  unfold prefR eqPrefix
  have e : ∀ i : Fin 10, (if i.val < j.val then bitFactor (rowBits s i) (a i) else 1) =
      (if i.val < j.val then (if bitR s.val i.val = true then A i.val else 1 - A i.val) else (1 : K)) := by
    intro i
    rw [hA i.val i.isLt]
    rfl
  symm
  rw [Finset.prod_congr rfl (fun i _ => e i),
    Fin.prod_univ_eq_prod_range
      (fun n => if n < j.val then (if bitR s.val n = true then A n else 1 - A n) else (1 : K)) 10,
    ← Finset.prod_range_mul_prod_Ico _ (show j.val ≤ 10 by omega),
    Finset.prod_eq_one (s := Finset.Ico j.val 10)
      (fun n hn => if_neg (by rw [Finset.mem_Ico] at hn; omega)), mul_one]
  apply Finset.prod_congr rfl
  intro n hn
  rw [if_pos (Finset.mem_range.1 hn)]

theorem pg_eq (c d : ℕ) (b w : K) :
    pgR c b w d = pcR b w (exR c) d + (if d = 0 then (if c = 10 then 1 else 0) else 0) := by
  unfold pgR
  split_ifs <;> simp_all

/-- One stored coefficient of the row model. -/
theorem row_cell (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (i u τ q : K) (c : ℕ) (hτ : rotR i u c = τ) (hq : q = if c = 10 then 1 else 0)
    (s : Fin 1024) (j : Fin 10) (kk : Fin 27) :
    (rowPoly τ q (famR c) (exR c) a s j).coeff (R1Z.RfChain.coeffOf kk).val =
      fullR (bitR s.val j.val) (fun d => pgR c (bR A (famR c) j.val s.val) (wR (famR c) j.val) d *
        prefR A j.val s.val * rotR i u c) (coeffR kk.val) := by
  rw [row_coeff, coeffOf_val]
  apply fullR_congr
  intro d
  have hw : (wR (famR c) j.val : K) = R0Z.PureRounds.w (famR c) j := rfl
  rw [bR_eq A a hA (famR c) j s, prefR_eq A a hA j s, pg_eq, hq, ← hτ, hw]
  ring

/-- The row model at every Z4c coordinate. -/
theorem zq_row (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (i u τ q : K) (c : ℕ) (hτ : rotR i u c = τ) (hq : q = if c = 10 then 1 else 0)
    (s : Fin 1024) (p : Fin 271) :
    zq (fun j => rowPoly τ q (famR c) (exR c) a s j) p = rrowR A i u c s.val p.val := by
  simp only [zq, rrowR]
  by_cases hp : p.val = 0
  · rw [if_pos hp, if_pos hp, row_eval, hq, ← hτ]
    unfold rotR
    split_ifs <;> ring
  · rw [if_neg hp, if_neg hp]
    exact row_cell A a hA i u τ q c hτ hq s _ _

/-! ### The D (Libra) rows -/

/-- `tail_row`'s variable as a `Fin 10`. -/
def kF (co : Fin 1024) : Fin 10 := ⟨mR co.val, by unfold mR; split_ifs <;> omega⟩

/-- The Libra round polynomials of transported coefficient `co`
(`R0Z.PureRounds.coordinate_power_round`, zero for `co ≥ 56`). -/
def tPoly (a : Fin 10 → K) (co : Fin 1024) (j : Fin 10) : K[X] :=
  if 56 ≤ co.val then 0
  else if j.val < (kF co).val then C ((2 : K) ^ (8 - j.val) * (if co.val % 28 = 0 then 2 else 1))
  else if j = kF co then C ((2 : K) ^ (9 - j.val)) * X ^ (co.val % 28)
  else C ((2 : K) ^ (9 - j.val) * a (kF co) ^ (co.val % 28))

theorem rounds_hw (ch : Challenges K) (co : Fin 1024) (j : Fin 10) :
    R0Z.PayloadSplit.rounds ch j (fun a => R1Z.RfOwn.rustHWeight a co) = tPoly (alpha ch) co j := by
  unfold tPoly
  by_cases h56 : 56 ≤ co.val
  · rw [if_pos h56]
    have e : (fun a : Fin 10 → K => R1Z.RfOwn.rustHWeight a co) = 0 := by
      funext a
      unfold R1Z.RfOwn.rustHWeight
      rw [if_neg (show ¬ co.val < 28 by omega), if_neg (show ¬ co.val < 56 by omega)]
      rfl
    rw [e, map_zero]
  · rw [if_neg h56]
    have e : (fun a : Fin 10 → K => R1Z.RfOwn.rustHWeight a co) =
        fun a => a (kF co) ^ (co.val % 28) := by
      funext a
      unfold R1Z.RfOwn.rustHWeight
      by_cases h : co.val < 28
      · have hk : kF co = 8 := Fin.ext (show mR co.val = 8 by unfold mR; rw [if_pos h])
        rw [if_pos h, hk, Nat.mod_eq_of_lt h]
      · have hk : kF co = 9 := Fin.ext (show mR co.val = 9 by unfold mR; rw [if_neg h])
        rw [if_neg h, if_pos (show co.val < 56 by omega), hk]
        congr 1
        omega
    rw [e]
    exact coordinate_power_round ch (kF co) j (co.val % 28) (by omega)

theorem coeffR_zero_iff (k : ℕ) : coeffR k = 0 ↔ k = 0 := by
  unfold coeffR
  by_cases hk : k = 0
  · rw [if_pos hk]
    exact ⟨fun _ => hk, fun _ => rfl⟩
  · rw [if_neg hk]
    exact ⟨fun h => absurd h (Nat.succ_ne_zero k), fun h => absurd h hk⟩

/-- One stored coefficient of the Libra model. -/
theorem tcell_eq (a : Fin 10 → K) (A : ℕ → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (co : Fin 1024) (h56 : ¬ 56 ≤ co.val) (j : Fin 10) (kk : Fin 27) :
    (tPoly a co j).coeff (coeffR kk.val) = tcellR A co.val j.val kk.val := by
  have hk : (kF co).val = mR co.val := rfl
  have ha : a (kF co) = A (mR co.val) := (hA (mR co.val) (kF co).isLt).symm
  unfold tPoly tcellR
  rw [if_neg h56, hk, ha]
  by_cases h1 : j.val < mR co.val
  · rw [if_pos h1, if_pos h1, coeff_C]
    by_cases hk0 : kk.val = 0
    · rw [if_pos ((coeffR_zero_iff _).2 hk0), if_pos hk0]
      push_cast
      ring
    · rw [if_neg (fun h => hk0 ((coeffR_zero_iff _).1 h)), if_neg hk0]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j.val = mR co.val
    · have hj : j = kF co := Fin.ext (by rw [hk]; exact h2)
      rw [if_pos hj, if_pos h2, coeff_C_mul_X_pow]
      have hc : coeffR kk.val = co.val % 28 ↔
          (co.val % 28 ≠ 1 ∧ kk.val = (if co.val % 28 = 0 then 0 else co.val % 28 - 1)) := by
        unfold coeffR
        constructor
        · intro h
          split_ifs at h ⊢ <;> omega
        · intro h
          split_ifs at h ⊢ <;> omega
      by_cases hcc : coeffR kk.val = co.val % 28
      · rw [if_pos hcc, if_pos (hc.1 hcc)]
        norm_cast
      · rw [if_neg hcc, if_neg (fun h => hcc (hc.2 h))]
    · have hj : ¬ j = kF co := fun h => h2 (by rw [h]; exact hk)
      rw [if_neg hj, if_neg h2, coeff_C]
      by_cases hk0 : kk.val = 0
      · rw [if_pos ((coeffR_zero_iff _).2 hk0), if_pos hk0]
        push_cast
        ring
      · rw [if_neg (fun h => hk0 ((coeffR_zero_iff _).1 h)), if_neg hk0]

/-- The Libra model at every Z4c coordinate. -/
theorem zq_tail (a : Fin 10 → K) (A : ℕ → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = a ⟨n, h⟩)
    (co : Fin 1024) (p : Fin 271) : zq (tPoly a co) p = trowR A co.val p.val := by
  by_cases h56 : 56 ≤ co.val
  · simp only [zq, trowR, tPoly, if_pos h56, eval_zero, coeff_zero, add_zero, ite_self]
  · have h0 : tPoly a co 0 = C ((2 : K) ^ (8 - (0 : Fin 10).val) * (if co.val % 28 = 0 then 2 else 1)) := by
      unfold tPoly
      rw [if_neg h56, if_pos (show (0 : Fin 10).val < (kF co).val by
        show 0 < mR co.val
        unfold mR
        split_ifs <;> omega)]
    simp only [zq, trowR]
    rw [if_neg h56]
    by_cases hp : p.val = 0
    · rw [if_pos hp, if_pos hp, h0, eval_C, eval_C, Fin.val_zero, Nat.sub_zero]
      ring
    · rw [if_neg hp, if_neg hp, if_neg (show ¬ 10 ≤ (p.val - 1) / 27 by have := p.isLt; omega), coeffOf_val]
      exact tcell_eq a A hA co h56 _ _

/-! ### The three source lanes -/

theorem ite_one_smul {V : Type*} [AddCommGroup V] [Module K V] (P : Prop) [Decidable P] (v : V) :
    (if P then v else 0) = (if P then (1 : K) else 0) • v := by
  split_ifs <;> simp

theorem rounds_maskOnlySrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (c : Fin 10) (r : Fin 1024) (hr : r ≠ 0) (j : Fin 10) :
    R0Z.PayloadSplit.rounds ch j (fun a => R0Z.PayloadSplit.maskLinear π B a
        (pureTrace B (maskOnlySrc (K := K) (F := F) c r))) =
      (1 : K) • (rowPoly (R0P.Mask.towerBasis B ⟨(16 + c.val) % 4, Nat.mod_lt _ (by omega)⟩) 0
          (famR c.val) (exR c.val) (alpha ch) r j -
        (if r ∈ copyInactiveRows then (1 : K) else 0) •
          rowPoly (R0P.Mask.towerBasis B ⟨(16 + c.val) % 4, Nat.mod_lt _ (by omega)⟩) 0
            (famR c.val) (exR c.val) (alpha ch) 0 j) := by
  have hfam : famR c.val = 0 := by
    unfold famR
    exact if_neg (by omega)
  have hex : exR c.val = (R0P.Mask.maskOnlyFactorExponent c).val := by
    unfold exR expR
    rw [if_neg (show ¬ c.val = 10 by omega)]
    fin_cases c <;> rfl
  have hs : ∀ l : Fin 29, l ≠ ⟨16 + c.val, by omega⟩ →
      pureTrace B (maskOnlySrc (K := K) (F := F) c r) l = 0 :=
    fun l hl => pureTrace_maskOnlySrc_other B c r l hl
  have hf : (fun a => R0Z.PayloadSplit.maskLinear π B a (pureTrace B (maskOnlySrc (K := K) (F := F) c r))) =
      fun a => R0P.Mask.towerBasis B ⟨(16 + c.val) % 4, Nat.mod_lt _ (by omega)⟩ *
        R0P.Mask.maskLinear 0 a ^ (R0P.Mask.maskOnlyFactorExponent c).val *
          ∑ s, selAt a s * balWord 0 r 1 s := by
    funext a
    rw [maskLinear_maskOnly π B a _ c hs, pureTrace_maskOnlySrc B c r hr]
  rw [hf, pureRound_maskOnly B ch c (balWord 0 r 1) j, sum_smul_balWord _ 0 r hr 1, hfam, hex]
  unfold rowPoly
  split_ifs <;> simp only [map_zero, zero_add, one_smul, zero_smul, sub_zero]

theorem rounds_gSrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) (j : Fin 10) :
    R0Z.PayloadSplit.rounds ch j (fun a => R0Z.PayloadSplit.maskLinear π B a
        (pureTrace B (gSrc (K := K) (F := F) r k))) =
      R0P.Mask.towerBasis B k • (rowPoly 1 1 (famR 10) (exR 10) (alpha ch) r j -
        (if r ∈ copyInactiveRows then (1 : K) else 0) • rowPoly 1 1 (famR 10) (exR 10) (alpha ch) 0 j) := by
  have hs : ∀ l : Fin 29, l ≠ 27 → pureTrace B (gSrc (K := K) (F := F) r k) l = 0 :=
    fun l hl => pureTrace_gSrc_other B r k l hl
  have hf : (fun a => R0Z.PayloadSplit.maskLinear π B a (pureTrace B (gSrc (K := K) (F := F) r k))) =
      fun a => (1 + R0P.Mask.maskLinear 16 a ^ 26) *
        ∑ s, selAt a s * balWord 0 r (R0P.Mask.towerBasis B k) s := by
    funext a
    rw [maskLinear_G π B a _ hs, pureTrace_gSrc B r k hr]
  have hfam : famR 10 = 16 := rfl
  have hex : exR 10 = 26 := rfl
  rw [hf, pureRound_G ch (balWord 0 r (R0P.Mask.towerBasis B k)) j, sum_smul_balWord _ 0 r hr, hfam, hex]
  unfold rowPoly
  split_ifs <;> simp only [map_one, one_mul, one_smul, zero_smul, sub_zero, smul_sub]

theorem rounds_dSrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) (j : Fin 10) :
    R0Z.PayloadSplit.rounds ch j (fun a => R0Z.PayloadSplit.maskLinear π B a
        (pureTrace B (dSrc (K := K) (F := F) r k))) =
      R0P.Mask.towerBasis B k • (tPoly (alpha ch) (π r) j -
        (if r ∈ copyInactiveRows then (1 : K) else 0) • tPoly (alpha ch) (π 0) j) := by
  have hs : ∀ l : Fin 29, l ≠ 28 → pureTrace B (dSrc (K := K) (F := F) r k) l = 0 :=
    fun l hl => pureTrace_dSrc_other B r k l hl
  have hf : (fun a => R0Z.PayloadSplit.maskLinear π B a (pureTrace B (dSrc (K := K) (F := F) r k))) =
      R0P.Mask.towerBasis B k • ((fun a => R1Z.RfOwn.rustHWeight a (π r)) -
        (if r ∈ copyInactiveRows then (1 : K) else 0) • (fun a => R1Z.RfOwn.rustHWeight a (π 0))) := by
    funext a
    rw [maskLinear_D π B a _ hs,
      R1Z.RfOwn.extra_balWord π a 28 _ 0 r hr _ (pureTrace_dSrc B r k hr)]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hf, map_smul, map_sub, map_smul, rounds_hw, rounds_hw]

/-- The lane dispatch of `CertOwn.mkSrc`. -/
def srcTape (c : ℕ) (r : Fin 1024) (k : Fin 4) : M K F :=
  if h : c < 10 then maskOnlySrc ⟨c, h⟩ r else if c = 10 then gSrc r k else dSrc r k

theorem towerBasis_tb (B : PackBasis F) (k : Fin 4) :
    R0P.Mask.towerBasis B k = tbR B.i B.u k.val := by
  fin_cases k <;> rfl

/-- **The pure-round closed form.**  For every lane, row `r ≠ 0` and limb `k`, the Z4c
coordinates of the source's round image are the Rust model `srcRoundR`. -/
theorem z4c_srcTape {Bat : Type} [BatchedLayer K Bat] (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (A : ℕ → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = alpha ch ⟨n, h⟩)
    (T : ℕ → ℕ) (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (Fl : ℕ → K) (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    (c : ℕ) (r : Fin 1024) (hr : r ≠ 0) (k : Fin 4) :
    R1Z.RfChain.z4c (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (srcTape c r k)) =
      fun p => srcRoundR A T Fl B.i B.u c r.val k.val p.val := by
  funext p
  have e1 : R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (srcTape (K := K) (F := F) c r k) =
      fun j (i : Fin 28) => (R0Z.PayloadSplit.rounds ch j (fun a => R0Z.PayloadSplit.maskLinear π B a
        (pureTrace B (srcTape (K := K) (F := F) c r k)))).coeff i.val :=
    funext fun j => funext fun i => roundMaskMap_coeff π B ch _ j i
  rw [e1, z4c_poly _ (fun j => rounds_natDegree_lt ch j _)]
  have hFr := hFl r
  have hT0 : T 0 = (π 0).val := by
    have := hT 0
    rwa [Fin.val_zero] at this
  unfold srcTape srcRoundR
  by_cases h1 : c < 10
  · rw [dif_pos h1, if_pos h1]
    have e2 := funext (rounds_maskOnlySrc π B ch ⟨c, h1⟩ r hr)
    have hq0 : (0 : K) = if c = 10 then 1 else 0 := by rw [if_neg (show ¬ c = 10 by omega)]
    rw [e2, zq_comb, zq_row A (alpha ch) hA B.i B.u _ 0 c ?_ hq0,
      zq_row A (alpha ch) hA B.i B.u _ 0 c ?_ hq0, hFr, Fin.val_zero]
    · ring
    · rw [towerBasis_tb]
      unfold rotR
      rw [if_neg (show ¬ c = 10 by omega)]
      show tbR B.i B.u (c % 4) = tbR B.i B.u ((16 + c) % 4)
      congr 1
      omega
    · rw [towerBasis_tb]
      unfold rotR
      rw [if_neg (show ¬ c = 10 by omega)]
      show tbR B.i B.u (c % 4) = tbR B.i B.u ((16 + c) % 4)
      congr 1
      omega
  · rw [dif_neg h1, if_neg h1]
    by_cases h2 : c = 10
    · subst h2
      rw [if_pos rfl, if_pos rfl]
      have e2 := funext (rounds_gSrc π B ch r k hr)
      have hτ : rotR B.i B.u 10 = 1 := if_pos rfl
      rw [e2, zq_comb, zq_row A (alpha ch) hA B.i B.u 1 1 10 hτ (if_pos rfl).symm,
        zq_row A (alpha ch) hA B.i B.u 1 1 10 hτ (if_pos rfl).symm, hFr, Fin.val_zero, towerBasis_tb]
    · rw [if_neg h2, if_neg h2]
      have e2 := funext (rounds_dSrc π B ch r k hr)
      rw [e2, zq_comb, zq_tail (alpha ch) A hA, zq_tail (alpha ch) A hA, hFr, hT r, hT0, towerBasis_tb]

/-! ### The column identification -/

theorem limbs_pack4' (B : PackBasis F) (hB : R0Z.K4.PackField B) (v : Fin 4 → F) :
    R1Z.RfChain.limbs B hB (pack4 B (fun l => (v l : K))) = v := by
  have hx : pack4 B (fun l => (v l : K)) ∈ R0Z.K4.K4 B hB :=
    (R0Z.K4.mem_K4_iff_pack4 B hB).2 ⟨_, fun j => (v j).2, rfl⟩
  have e := R1Z.RfChain.pack4_limbs B hB hx
  have hz : pack4 B (fun l => ((R1Z.RfChain.limbs B hB (pack4 B (fun l => (v l : K))) l : K) - (v l : K))) = 0 := by
    have hs : pack4 B (fun l => ((R1Z.RfChain.limbs B hB (pack4 B (fun l => (v l : K))) l : K) - (v l : K))) =
        pack4 B (fun l => (R1Z.RfChain.limbs B hB (pack4 B (fun l => (v l : K))) l : K)) -
          pack4 B (fun l => (v l : K)) := by
      unfold pack4
      ring
    rw [hs, e, sub_self]
  have := (pack4_eq_zero_iff B _ (fun j => F.sub_mem (R1Z.RfChain.limbs B hB _ j).2 (v j).2)).1 hz
  funext l
  exact Subtype.ext (sub_eq_zero.1 (this l))

theorem flat_of_pack (B : PackBasis F) (hB : R0Z.K4.PackField B) (φ : R1Z.CertData.ZP →+* ↥F)
    (m : ℕ → R1Z.CertData.ZP) (s t : ℕ) (V : Fin 271 → K)
    (h : ∀ p : Fin 271, pack4 B (fun l : Fin 4 => ((φ (m (t * s + (4 * p.val + l.val))) : F) : K)) = V p)
    (i : Fin 1084) : R1Z.RfChain.flat B hB V i = φ (R1Z.CertData.colM m s i t) := by
  have hi : 4 * (R1Z.RfChain.fpe.symm i).1.val + (R1Z.RfChain.fpe.symm i).2.val = i.val := by
    have e := congrArg Fin.val (R1Z.RfChain.fpe.apply_symm_apply i)
    have hv : ∀ (q : Fin 271) (l : Fin 4), (R1Z.RfChain.fpe (q, l)).val = l.val + 4 * q.val := by
      intro q l
      simp [R1Z.RfChain.fpe, finProdFinEquiv]
    rw [hv] at e
    omega
  unfold R1Z.RfChain.flat R1Z.CertData.colM
  rw [← h, limbs_pack4']
  simp only [hi]

/-- **`round_ident`**: the `hRound` shape from the column entry premise. -/
theorem round_ident {Bat : Type} [BatchedLayer K Bat] (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (hB : R0Z.K4.PackField B) (ch : Challenges K) (φ : R1Z.CertData.ZP →+* ↥F)
    (A : ℕ → K) (hA : ∀ (n : ℕ) (h : n < 10), A n = alpha ch ⟨n, h⟩)
    (T : ℕ → ℕ) (hT : ∀ r : Fin 1024, T r.val = (π r).val)
    (Fl : ℕ → K) (hFl : ∀ r : Fin 1024, Fl r.val = if r ∈ copyInactiveRows then 1 else 0)
    {N : ℕ} (src : Fin N → M K F) (Ln : ℕ → ℕ) (Rw : ℕ → Fin 1024) (Lb : ℕ → Fin 4)
    (hsrc : ∀ t : Fin N, src t = srcTape (Ln t.val) (Rw t.val) (Lb t.val))
    (hR0 : ∀ t : Fin N, Rw t.val ≠ 0) (m : ℕ → R1Z.CertData.ZP) (s : ℕ)
    (hent : ∀ (t : Fin N) (p : Fin 271),
      pack4 B (fun l : Fin 4 => ((φ (m (t.val * s + (4 * p.val + l.val))) : F) : K)) =
        srcRoundR A T Fl B.i B.u (Ln t.val) (Rw t.val).val (Lb t.val).val p.val) :
    ∀ (i : Fin 1084) (t : Fin N),
      R1Z.RfChain.flat B hB (R1Z.RfChain.z4c (R0Z.Z4Maps.roundMaskMap (Bat := Bat) π B ch (src t))) i =
        φ (R1Z.CertData.colM m s i t) := by
  intro i t
  rw [hsrc t, z4c_srcTape π B ch A hA T hT Fl hFl _ _ (hR0 t)]
  exact flat_of_pack B hB φ m s t.val _ (hent t) i

#print axioms sum_smul_balWord
#print axioms roundMaskMap_coeff
#print axioms z4c_poly
#print axioms zq_comb
#print axioms row_coeff
#print axioms boolR_split
#print axioms row_eval
#print axioms bR_eq
#print axioms prefR_eq
#print axioms row_cell
#print axioms zq_row
#print axioms rounds_hw
#print axioms tcell_eq
#print axioms zq_tail
#print axioms rounds_maskOnlySrc
#print axioms rounds_gSrc
#print axioms rounds_dSrc
#print axioms z4c_srcTape
#print axioms flat_of_pack
#print axioms round_ident

end R1Z.CertRound

end
