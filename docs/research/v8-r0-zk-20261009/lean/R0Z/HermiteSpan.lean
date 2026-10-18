import Mathlib

/-! J5a (DESIGN-T2b-2b §2.3.2, §5): generic polynomial span facts P1–P4.
Mathlib only; no protocol object is imported, so the file is payload-generic
(R0 and R1).  `K` is any field, `F` any ring acting on `K`; the numeric
parameters are variables, and the R0 degrees (e ≤ 26, m = 26, d = 27) appear
only in the corollaries at the end, under the premise `∀ n ≤ 28, (n ! : K) ≠ 0`.

Notation: `L = C w * X + C β` (w ≠ 0), β : Fin n → K injective.

Method (one core lemma).  For a degree frame `N` and a sequence `s : ℕ → K`
put `apolar w N s = Σ_{d ≤ N} C(N,d)·s(N−d)·w^d·X^d` and
`pair N q s = Σ_{k ≤ N} q_k·s_k`.  Then `L^N = apolar (β^·)`,
`(N)·L^(N−1) = apolar (k·β^(k−1))`, `1 = apolar (δ_N)`.  `top_cover`: if the
generators are `apolar (s_j)` up to corrections of degree `< N+1−r`, and no
nonzero `q` of degree `< r` is `pair`-orthogonal to every `s_j`, then for each
degree `D ∈ [N+1−r, N]` the K-span contains an element of degree `≤ D` with any
prescribed coefficient at `D`.  Separation is: `n` distinct roots (P1, P3a),
`n` distinct double roots (P2, P3b).

Precise statements (all proved below; no conditional premise except the
factorial / binomial nonvanishing, which is needed: in characteristic p ≤ N the
binomials C(N,k) can vanish and every dimension count below can fail).

P4  `coeff_cover`  V : Submodule F K[X];  if ∀ D ∈ [m, d], ∀ a : K,
      ∃ v ∈ V, natDegree v ≤ D ∧ coeff v D = a,  then
      ∀ p, natDegree p ≤ d → ∃ v ∈ V, degree (p − v) < m.
    `coeff_cover_of_leadingCoeff_span`  span_F {leadingCoeff v | v ∈ V,
      natDegree v = D} = ⊤ gives the per-degree hypothesis.
    `leading_coeff_cover`  the design's form: leading coefficients at every
      D ∈ [m, d] span K over F ⇒ the conclusion above.
    `leading_coeff_cover_root`  m = 1 and every v ∈ V vanishes at α:
      p(α) = 0 ∧ natDegree p ≤ d ⇒ p ∈ V   (the §2.3.6 upward step).
P1  `divided_difference_degree`  (e ! ≠ 0): ∀ k < min n (e+1), ∃ p ∈
      span_K{L_i^e}, natDegree p = e − k ∧ leadingCoeff p = C(e,k)·w^(e−k).
    `powers_finrank`  finrank span_K{L_i^e} = min n (e+1).
P2  `hermite_span_eq`  span{L_i^e, X·L_i^e} = span{L_i^e, L_i·L_i^e}.
    `hermite_top_cover` ((e+1)! ≠ 0): ∀ D ∈ [e+2 − min(2n, e+2), e+1], ∀ a,
      ∃ p ∈ span{L_i^e, X L_i^e}, natDegree p ≤ D ∧ coeff p D = a.
    `hermite_span_dim`  finrank span{L_i^e, X L_i^e} = min (2n) (e+2).
    `hermite_linearIndependent`  2n ≤ e+2 ⇒ the 2n polynomials are independent.
P3a `gfactor_top_cover`, `gfactor_span_dim`  (1 ≤ m, m ! ≠ 0) for 1 + L_i^m:
      cover of D ∈ [m+1 − min(n, m+1), m]; finrank = min n (m+1).
P3b `gfactor_hermite_top_cover` ((m+1)! ≠ 0) for {Φ_i, X·Φ_i}, Φ_i = 1 + L_i^m:
      cover of D ∈ [m+2 − min(2n, m), m+1]  (degrees ≥ 2 only);
    `gfactor_hermite_linearIndependent`  2n ≤ m ⇒ independent.
    STOP (design text false as written): "P3 … resp. min(2n, 28)" — the
    dimension of span{Φ_i, XΦ_i} is NOT min(2n, m+2) for all distinct β.
    The constants 1 and L in Φ, LΦ couple the two lowest coefficients to the
    nodes; at 2n ≥ m+1 the low 2×2 block can be singular.  Counterexamples
    (exact rank, scratch script ce.py):
      m = 2, n = 2, K = GF(5) (2!,3! ≠ 0), w = 1, β = (0, 1): rank 3 < 4
        (by hand: det = −t²(t²+4) with β = (0, t); t² = −4 = 1 in GF(5));
      m = 26, n = 14, K = GF(101) (all n! ≠ 0 for n ≤ 28), w = 1,
        β = (92,3,67,28,97,56,63,70,29,44,86,58,37,23): rank 27 < 28.
    So only the restricted form r ≤ min(2n, m) is structural.  P3a (Φ alone,
    min(n, m+1)) is unconditional and is what the fresh-G pivots use.

Corollaries (R0 degrees, premise `hfac : ∀ n ≤ 28, (n ! : K) ≠ 0`):
  `divided_difference_degree_R0` (e ≤ 26), `powers_finrank_R0`,
  `hermite_span_dim_R0` (e ≤ 26), `hermite_top_cover_R0`,
  `gfactor_span_dim_R0` (m = 26: min n 27), `gfactor_top_cover_R0`,
  `gfactor_hermite_top_cover_R0` (D ∈ [28 − min(2n,26), 27]),
  `gfactor_hermite_linearIndependent_R0` (n ≤ 13).
-/
set_option autoImplicit false
noncomputable section
namespace R0Z.HermiteSpan
open Polynomial Finset Module
open scoped Nat Matrix

variable {K : Type*} [Field K]

/-! ### Factorial premises -/

lemma choose_cast_ne_zero {N : ℕ} (h : (N ! : K) ≠ 0) {k : ℕ} (hk : k ≤ N) :
    (N.choose k : K) ≠ 0 := by
  intro h0
  apply h
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  rw [h0, zero_mul, zero_mul]

lemma natCast_ne_zero_of_factorial {N : ℕ} (h : (N ! : K) ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ N) : (k : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hk hkN
  intro h0
  apply h
  rw [hc]
  push_cast
  rw [h0, zero_mul]

lemma factorial_ne_zero_of_le {N M : ℕ} (h : (N ! : K) ≠ 0) (hM : M ≤ N) :
    (M ! : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hM
  intro h0
  apply h
  rw [hc]
  push_cast
  rw [h0, zero_mul]

/-! ### P4: triangular elimination over an arbitrary scalar ring -/

theorem coeff_cover {F : Type*} [Ring F] [Module F K] (V : Submodule F K[X]) (m d : ℕ)
    (hV : ∀ D, m ≤ D → D ≤ d → ∀ a : K, ∃ v ∈ V, v.natDegree ≤ D ∧ v.coeff D = a) :
    ∀ p : K[X], p.natDegree ≤ d → ∃ v ∈ V, (p - v).degree < m := by
  have key : ∀ D : ℕ, ∀ p : K[X], p.degree < D → D ≤ d + 1 →
      ∃ v ∈ V, (p - v).degree < m := by
    intro D
    induction D with
    | zero =>
      intro p hp _
      refine ⟨0, V.zero_mem, ?_⟩
      rw [sub_zero]
      exact lt_of_lt_of_le hp (by exact_mod_cast Nat.zero_le m)
    | succ D ih =>
      intro p hp hD
      by_cases hDm : D < m
      · refine ⟨0, V.zero_mem, ?_⟩
        rw [sub_zero]
        exact lt_of_lt_of_le hp (by exact_mod_cast (show D + 1 ≤ m by omega))
      · obtain ⟨v₁, hv₁, hv₁d, hv₁c⟩ := hV D (by omega) (by omega) (p.coeff D)
        have hlow : (p - v₁).degree < D := by
          rw [degree_lt_iff_coeff_zero]
          intro i hi
          rw [coeff_sub]
          rcases Nat.eq_or_lt_of_le hi with h | h
          · rw [← h, hv₁c, sub_self]
          · rw [coeff_eq_zero_of_degree_lt
                (lt_of_lt_of_le hp (by exact_mod_cast (show D + 1 ≤ i by omega))),
              coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hv₁d h), sub_zero]
        obtain ⟨v₂, hv₂, hv₂d⟩ := ih (p - v₁) hlow (by omega)
        refine ⟨v₁ + v₂, V.add_mem hv₁ hv₂, ?_⟩
        have : p - (v₁ + v₂) = p - v₁ - v₂ := by ring
        rw [this]
        exact hv₂d
  intro p hp
  refine key (d + 1) p ?_ le_rfl
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem coeff_cover_of_leadingCoeff_span {F : Type*} [Ring F] [Module F K]
    (V : Submodule F K[X]) (D : ℕ)
    (h : Submodule.span F {a : K | ∃ v ∈ V, v.natDegree = D ∧ v.leadingCoeff = a} = ⊤)
    (a : K) : ∃ v ∈ V, v.natDegree ≤ D ∧ v.coeff D = a := by
  let T : Submodule F K :=
    { carrier := {a : K | ∃ v ∈ V, v.natDegree ≤ D ∧ v.coeff D = a}
      add_mem' := by
        rintro _ _ ⟨v₁, h₁, d₁, rfl⟩ ⟨v₂, h₂, d₂, rfl⟩
        exact ⟨v₁ + v₂, V.add_mem h₁ h₂, natDegree_add_le_of_degree_le d₁ d₂, coeff_add _ _ _⟩
      zero_mem' := ⟨0, V.zero_mem, by simp, by simp⟩
      smul_mem' := by
        rintro c _ ⟨v, hv, hd, rfl⟩
        exact ⟨c • v, V.smul_mem c hv, (natDegree_smul_le c v).trans hd, coeff_smul _ _ _⟩ }
  have hle : Submodule.span F {a : K | ∃ v ∈ V, v.natDegree = D ∧ v.leadingCoeff = a} ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, hd, rfl⟩
    exact ⟨v, hv, hd.le, by rw [leadingCoeff, hd]⟩
  rw [h] at hle
  exact hle (Submodule.mem_top (x := a))

/-- P4 in the design's form. -/
theorem leading_coeff_cover {F : Type*} [Ring F] [Module F K] (V : Submodule F K[X])
    (m d : ℕ)
    (hlead : ∀ D, m ≤ D → D ≤ d →
      Submodule.span F {a : K | ∃ v ∈ V, v.natDegree = D ∧ v.leadingCoeff = a} = ⊤) :
    ∀ p : K[X], p.natDegree ≤ d → ∃ v ∈ V, (p - v).degree < m :=
  coeff_cover V m d fun D h1 h2 a => coeff_cover_of_leadingCoeff_span V D (hlead D h1 h2) a

/-- P4 at m = 1 with the degree-0 coefficient fixed by a common root. -/
theorem leading_coeff_cover_root {F : Type*} [Ring F] [Module F K] (V : Submodule F K[X])
    (d : ℕ) (α : K) (hV0 : ∀ v ∈ V, v.eval α = 0)
    (hV : ∀ D, 1 ≤ D → D ≤ d → ∀ a : K, ∃ v ∈ V, v.natDegree ≤ D ∧ v.coeff D = a)
    (p : K[X]) (hp : p.eval α = 0) (hpd : p.natDegree ≤ d) : p ∈ V := by
  obtain ⟨v, hv, hlt⟩ := coeff_cover V 1 d hV p hpd
  have h0 : (p - v).degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.1 (by exact_mod_cast hlt)
  have hC := eq_C_of_degree_le_zero h0
  have hev : (p - v).eval α = 0 := by rw [eval_sub, hp, hV0 v hv, sub_zero]
  rw [hC, eval_C] at hev
  rw [hev, C_0, sub_eq_zero] at hC
  rw [hC]
  exact hv

/-! ### The apolar transform and the pairing -/

/-- `Σ_{d ≤ N} C(N,d) · s(N−d) · w^d · X^d`. -/
def apolar (w : K) (N : ℕ) (s : ℕ → K) : K[X] :=
  ∑ d ∈ range (N + 1), C ((N.choose d : K) * s (N - d) * w ^ d) * X ^ d

/-- `Σ_{k ≤ N} q_k · s_k`. -/
def pair (N : ℕ) (q : K[X]) (s : ℕ → K) : K :=
  ∑ k ∈ range (N + 1), q.coeff k * s k

lemma coeff_apolar (w : K) (N : ℕ) (s : ℕ → K) (i : ℕ) :
    (apolar w N s).coeff i =
      if i < N + 1 then (N.choose i : K) * s (N - i) * w ^ i else 0 := by
  unfold apolar
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

lemma apolar_mem_degreeLT (w : K) (N : ℕ) (s : ℕ → K) :
    apolar w N s ∈ degreeLT K (N + 1) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_apolar, if_neg (by omega)]

lemma apolar_add (w : K) (N : ℕ) (s t : ℕ → K) :
    apolar w N (fun k => s k + t k) = apolar w N s + apolar w N t := by
  unfold apolar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_add, add_mul, map_add, add_mul]

lemma apolar_indicator (w : K) (N : ℕ) :
    apolar w N (fun k => if k = N then 1 else 0) = 1 := by
  unfold apolar
  rw [Finset.sum_eq_single 0]
  · simp
  · intro d hd hd0
    have : N - d ≠ N := by have := Finset.mem_range.1 hd; omega
    simp [this]
  · intro h
    simp at h

/-- `L^N` is the transform of the evaluation sequence. -/
lemma apolar_pow (w b : K) (N : ℕ) :
    apolar w N (fun k => b ^ k) = (C w * X + C b) ^ N := by
  unfold apolar
  rw [add_pow]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [map_mul, map_pow, map_natCast, mul_pow]
  ring

/-- `L^e` is the transform (frame `e+1`) of the scaled derivative sequence. -/
lemma apolar_pow_pred (w b : K) (e : ℕ) (he : ((e + 1 : ℕ) : K) ≠ 0) :
    apolar w (e + 1) (fun k => ((e + 1 : ℕ) : K)⁻¹ * ((k : K) * b ^ (k - 1))) =
      (C w * X + C b) ^ e := by
  unfold apolar
  rw [Finset.sum_range_succ, add_pow]
  have hlast : C (((e + 1).choose (e + 1) : K) *
      (((e + 1 : ℕ) : K)⁻¹ * (((e + 1 - (e + 1) : ℕ) : K) * b ^ (e + 1 - (e + 1) - 1))) *
      w ^ (e + 1)) * X ^ (e + 1) = 0 := by simp
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d < e + 1 := Finset.mem_range.1 hd
  have h1 : ((e + 1).choose d : K) * ((e + 1 - d : ℕ) : K) =
      (e.choose d : K) * ((e + 1 : ℕ) : K) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, (Nat.choose_mul_succ_eq e d).symm]
  have h2 : e + 1 - d - 1 = e - d := by omega
  have hrhs : C ((e.choose d : K) * b ^ (e - d) * w ^ d) * X ^ d =
      (C w * X) ^ d * C b ^ (e - d) * (e.choose d : K[X]) := by
    simp only [map_mul, map_pow, map_natCast, mul_pow]
    ring
  rw [← hrhs]
  congr 2
  dsimp only
  rw [h2]
  calc ((e + 1).choose d : K) * (((e + 1 : ℕ) : K)⁻¹ * (((e + 1 - d : ℕ) : K) * b ^ (e - d))) *
        w ^ d
      = ((e + 1).choose d : K) * ((e + 1 - d : ℕ) : K) * ((e + 1 : ℕ) : K)⁻¹ * b ^ (e - d) *
          w ^ d := by ring
    _ = (e.choose d : K) * (((e + 1 : ℕ) : K) * ((e + 1 : ℕ) : K)⁻¹) * b ^ (e - d) * w ^ d := by
          rw [h1]; ring
    _ = (e.choose d : K) * b ^ (e - d) * w ^ d := by rw [mul_inv_cancel₀ he, mul_one]

lemma pair_pow {N : ℕ} {q : K[X]} (hq : q.natDegree < N + 1) (b : K) :
    pair N q (fun k => b ^ k) = q.eval b := by
  rw [pair, eval_eq_sum_range' hq]

lemma pair_deriv {N : ℕ} {q : K[X]} (hq : q.natDegree < N + 1) (c b : K) :
    pair N q (fun k => c * ((k : K) * b ^ (k - 1))) = c * (derivative q).eval b := by
  rw [derivative_eval, sum_over_range' q (f := fun n a => a * (n : K) * b ^ (n - 1))
    (fun n => by simp) (N + 1) hq, pair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma pair_add {N : ℕ} (q : K[X]) (s t : ℕ → K) :
    pair N q (fun k => s k + t k) = pair N q s + pair N q t := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma pair_indicator {N : ℕ} (q : K[X]) :
    pair N q (fun k => if k = N then 1 else 0) = q.coeff N := by
  unfold pair
  simp

/-! ### Core: duality and the top cover -/

lemma exists_dual {ι : Type*} [Fintype ι] (N r : ℕ) (s : ι → ℕ → K)
    (hsep : ∀ q : K[X], q.degree < r → (∀ j, pair N q (s j) = 0) → q = 0)
    (k : ℕ) (hk : k < r) (hkN : k ≤ N) :
    ∃ c : ι → K, ∀ i ≤ k, ∑ j, c j * s j i = if i = k then 1 else 0 := by
  let M : Matrix (Fin (k + 1)) ι K := Matrix.of fun i j => s j i
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    let q : degreeLT K (k + 1) := (degreeLTEquiv K (k + 1)).symm t
    have hqc : ∀ i : Fin (k + 1), (q : K[X]).coeff i = t i := fun i => by
      have h := congrFun ((degreeLTEquiv K (k + 1)).apply_symm_apply t) i
      exact h
    have hqd : (q : K[X]).degree < ((k + 1 : ℕ) : WithBot ℕ) := mem_degreeLT.1 q.2
    have hpair : ∀ j, pair N (q : K[X]) (s j) = 0 := by
      intro j
      have hj := congrFun ht j
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Matrix.of_apply, M, Pi.zero_apply] at hj
      have hsum : pair N (q : K[X]) (s j) =
          ∑ i ∈ range (k + 1), (q : K[X]).coeff i * s j i := by
        unfold pair
        refine (Finset.sum_subset (f := fun i => (q : K[X]).coeff i * s j i)
          (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
        intro i _ hi
        have hi' : k + 1 ≤ i := by simpa using hi
        show (q : K[X]).coeff i * s j i = 0
        rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hqd (by exact_mod_cast hi')), zero_mul]
      rw [hsum, Finset.sum_range]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hj
      rw [hqc i, mul_comm]
    have hq0 := hsep q (lt_of_lt_of_le hqd (by exact_mod_cast (show k + 1 ≤ r by omega))) hpair
    funext i
    rw [← hqc i, hq0, coeff_zero]
    rfl
  have hrank : M.rank = k + 1 := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hinj,
      Module.finrank_fin_fun K]
  have htop : LinearMap.range M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hrank.trans (Module.finrank_fin_fun K).symm)
  obtain ⟨c, hc⟩ : (Pi.single (Fin.last k) 1 : Fin (k + 1) → K) ∈
      LinearMap.range M.mulVecLin := by
    rw [htop]; exact Submodule.mem_top
  refine ⟨c, fun i hi => ?_⟩
  have h := congrFun hc ⟨i, by omega⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, M] at h
  rw [Finset.sum_congr rfl fun j _ => mul_comm (c j) (s j i), h, Pi.single_apply]
  simp [Fin.ext_iff]

/-- The core: top-degree cover of the span of transformed generators. -/
theorem top_cover {ι : Type*} [Fintype ι] {w : K} (hw : w ≠ 0) {N r : ℕ} (hr : r ≤ N + 1)
    (hch : ∀ k ≤ N, (N.choose k : K) ≠ 0) (g : ι → K[X]) (s : ι → ℕ → K)
    (hg : ∀ j, (g j - apolar w N (s j)).degree < ((N + 1 - r : ℕ) : WithBot ℕ))
    (hsep : ∀ q : K[X], q.degree < r → (∀ j, pair N q (s j) = 0) → q = 0) :
    ∀ D, N + 1 - r ≤ D → D ≤ N → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range g), p.natDegree ≤ D ∧ p.coeff D = a := by
  intro D hD1 hD2 a
  obtain ⟨c, hc⟩ := exists_dual N r s hsep (N - D) (by omega) (by omega)
  have hb : (N.choose D : K) * w ^ D ≠ 0 := mul_ne_zero (hch D hD2) (pow_ne_zero _ hw)
  have hgc : ∀ j i, N + 1 - r ≤ i → (g j).coeff i = (apolar w N (s j)).coeff i := by
    intro j i hi
    have h := coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hg j) (by exact_mod_cast hi))
    rw [coeff_sub] at h
    exact sub_eq_zero.1 h
  set p : K[X] := ∑ j, (a / ((N.choose D : K) * w ^ D) * c j) • g j with hp
  have hmem : p ∈ Submodule.span K (Set.range g) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcoef : ∀ i, D ≤ i → p.coeff i = if i < N + 1 then
      a / ((N.choose D : K) * w ^ D) * ((N.choose i : K) * w ^ i) * ∑ j, c j * s j (N - i)
      else 0 := by
    intro i hi
    rw [hp, finsetSum_coeff]
    simp only [coeff_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => by rw [hgc j i (by omega), coeff_apolar]]
    split_ifs with h
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · simp
  refine ⟨p, hmem, ?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hcoef i hi.le]
    split_ifs with h
    · rw [hc (N - i) (by omega), if_neg (by omega), mul_zero]
    · rfl
  · rw [hcoef D le_rfl, if_pos (by omega), hc (N - D) le_rfl, if_pos rfl, mul_one,
      div_mul_cancel₀ a hb]

/-! ### Dimension consequences of the core -/

instance degreeLT_finiteDimensional (n : ℕ) : FiniteDimensional K (degreeLT K n) :=
  LinearEquiv.finiteDimensional (degreeLTEquiv K n).symm

lemma finrank_degreeLT_eq (n : ℕ) : finrank K (degreeLT K n) = n :=
  (degreeLTEquiv K n).finrank_eq.trans (Module.finrank_fin_fun K)

lemma natDegree_le_of_degree_lt {p : K[X]} {N : ℕ} (h : p.degree < ((N + 1 : ℕ) : WithBot ℕ)) :
    p.natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h (by exact_mod_cast (show N + 1 ≤ i by omega)))

theorem le_finrank_of_top_cover {ι : Type*} [Fintype ι] {w : K} (hw : w ≠ 0) {N r : ℕ}
    (hr : r ≤ N + 1) (hch : ∀ k ≤ N, (N.choose k : K) ≠ 0) (g : ι → K[X]) (s : ι → ℕ → K)
    (hg : ∀ j, (g j - apolar w N (s j)).degree < ((N + 1 - r : ℕ) : WithBot ℕ))
    (hsep : ∀ q : K[X], q.degree < r → (∀ j, pair N q (s j) = 0) → q = 0) :
    r ≤ finrank K (Submodule.span K (Set.range g)) := by
  have hcov := top_cover hw hr hch g s hg hsep
  haveI : FiniteDimensional K (Submodule.span K (Set.range g)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range g)
  have hle : degreeLT K (N + 1) ≤ Submodule.span K (Set.range g) ⊔ degreeLT K (N + 1 - r) := by
    intro t ht
    obtain ⟨p, hp, hlt⟩ := coeff_cover (Submodule.span K (Set.range g)) (N + 1 - r) N hcov t
      (natDegree_le_of_degree_lt (mem_degreeLT.1 ht))
    have : t = p + (t - p) := by ring
    rw [this]
    exact Submodule.add_mem_sup hp (mem_degreeLT.2 hlt)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span K (Set.range g))
    (degreeLT K (N + 1 - r))
  rw [finrank_degreeLT_eq] at h1 h2
  omega

theorem finrank_eq_min_of_sep {ι : Type*} [Fintype ι] {w : K} (hw : w ≠ 0) {N : ℕ}
    (hch : ∀ k ≤ N, (N.choose k : K) ≠ 0) (g : ι → K[X]) (s : ι → ℕ → K)
    (hg : ∀ j, (g j - apolar w N (s j)).degree <
      ((N + 1 - min (Fintype.card ι) (N + 1) : ℕ) : WithBot ℕ))
    (hsep : ∀ q : K[X], q.degree < (min (Fintype.card ι) (N + 1) : ℕ) →
      (∀ j, pair N q (s j) = 0) → q = 0) :
    finrank K (Submodule.span K (Set.range g)) = min (Fintype.card ι) (N + 1) := by
  have hlo := le_finrank_of_top_cover hw (min_le_right _ _) hch g s hg hsep
  have hup1 : finrank K (Submodule.span K (Set.range g)) ≤ Fintype.card ι :=
    finrank_range_le_card g
  have hspan : Submodule.span K (Set.range g) ≤ degreeLT K (N + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : g j = apolar w N (s j) + (g j - apolar w N (s j)) := by ring
    rw [hj]
    refine (degreeLT K (N + 1)).add_mem (apolar_mem_degreeLT w N (s j)) ?_
    rw [mem_degreeLT]
    exact lt_of_lt_of_le (hg j) (by exact_mod_cast (show N + 1 - min (Fintype.card ι) (N + 1)
      ≤ N + 1 by omega))
  have hup2 := Submodule.finrank_mono hspan
  rw [finrank_degreeLT_eq] at hup2
  omega

/-! ### Separation: simple and double roots -/

lemma eq_zero_of_double_roots {n : ℕ} (β : Fin n → K) (hβ : Function.Injective β) (q : K[X])
    (h0 : ∀ i, q.eval (β i) = 0) (h1 : ∀ i, (derivative q).eval (β i) = 0)
    (hdeg : q.natDegree < 2 * n) : q = 0 := by
  by_contra hq
  have hdvd : ∀ i, (X - C (β i)) ^ 2 ∣ q := fun i => by
    have h := (one_lt_rootMultiplicity_iff_isRoot hq).2 ⟨h0 i, h1 i⟩
    exact (le_rootMultiplicity_iff hq).1 (by omega)
  have hcop : Pairwise (Function.onFun IsCoprime fun i => (X - C (β i)) ^ 2) := fun i j hij =>
    (pairwise_coprime_X_sub_C hβ hij).pow
  have hprod := Fintype.prod_dvd_of_coprime hcop hdvd
  have hdeg' := natDegree_le_of_dvd hprod hq
  rw [natDegree_prod_of_monic (h := fun i _ => (monic_X_sub_C (β i)).pow 2)] at hdeg'
  simp only [natDegree_pow, natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hdeg'
  omega

lemma simple_sep {n e r : ℕ} (β : Fin n → K) (hβ : Function.Injective β) (hr1 : r ≤ n)
    (hr2 : r ≤ e + 1) :
    ∀ q : K[X], q.degree < r → (∀ j, pair e q (fun k => β j ^ k) = 0) → q = 0 := by
  intro q hq hj
  rcases eq_or_ne q 0 with h | h
  · exact h
  have hlt := (natDegree_lt_iff_degree_lt h).2 hq
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero q hβ (fun i => ?_) (by simp; omega)
  have := hj i
  rwa [pair_pow (by omega)] at this

/-- The Hermite sequences in frame `e+1`: scaled derivative (for `L^e`) and
evaluation (for `L^(e+1)`). -/
def hermS (e : ℕ) {n : ℕ} (β : Fin n → K) : Fin n ⊕ Fin n → ℕ → K :=
  Sum.elim (fun i k => ((e + 1 : ℕ) : K)⁻¹ * ((k : K) * β i ^ (k - 1))) (fun i k => β i ^ k)

lemma hermite_sep {n e r : ℕ} (β : Fin n → K) (hβ : Function.Injective β)
    (he : ((e + 1 : ℕ) : K) ≠ 0) (hr1 : r ≤ 2 * n) (hr2 : r ≤ e + 2) :
    ∀ q : K[X], q.degree < r → (∀ j, pair (e + 1) q (hermS e β j) = 0) → q = 0 := by
  intro q hq hj
  rcases eq_or_ne q 0 with h | h
  · exact h
  have hlt := (natDegree_lt_iff_degree_lt h).2 hq
  refine eq_zero_of_double_roots β hβ q (fun i => ?_) (fun i => ?_) (by omega)
  · have h1 : pair (e + 1) q (fun k => β i ^ k) = 0 := hj (Sum.inr i)
    rwa [pair_pow (by omega)] at h1
  · have h1 : pair (e + 1) q (fun k => ((e + 1 : ℕ) : K)⁻¹ * ((k : K) * β i ^ (k - 1))) = 0 :=
      hj (Sum.inl i)
    rw [pair_deriv (by omega)] at h1
    exact (mul_eq_zero.1 h1).resolve_left (inv_ne_zero he)

/-! ### Span equality: `X·f` versus `L·f` -/

lemma span_X_mul_eq {ι : Type*} {w : K} (hw : w ≠ 0) (β : ι → K) (f : ι → K[X]) :
    Submodule.span K (Set.range (Sum.elim f (fun i => X * f i))) =
      Submodule.span K (Set.range (Sum.elim f (fun i => (C w * X + C (β i)) * f i))) := by
  have hCC : C w⁻¹ * C w = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hw, C_1]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · have hx : (Sum.elim f (fun i => X * f i)) (Sum.inr i) =
          w⁻¹ • (C w * X + C (β i)) * f i - (w⁻¹ * β i) • f i := by
        simp only [Sum.elim_inr, smul_eq_C_mul, C_mul]
        linear_combination (-(X * f i)) * hCC
      rw [hx]
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · have hx : (Sum.elim f (fun i => (C w * X + C (β i)) * f i)) (Sum.inr i) =
          w • (X * f i) + β i • f i := by
        simp only [Sum.elim_inr, smul_eq_C_mul]
        ring
      rw [hx]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))

/-! ### P1: powers of distinct shifts -/

theorem powers_top_cover {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : (e ! : K) ≠ 0) :
    ∀ D, e + 1 - min n (e + 1) ≤ D → D ≤ e → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range fun i => (C w * X + C (β i)) ^ e),
        p.natDegree ≤ D ∧ p.coeff D = a :=
  top_cover hw (min_le_right _ _) (fun k hk => choose_cast_ne_zero hfac hk) _
    (fun i k => β i ^ k)
    (fun j => by rw [apolar_pow, sub_self, degree_zero]; exact WithBot.bot_lt_coe _)
    (simple_sep β hβ (min_le_left _ _) (min_le_right _ _))

theorem divided_difference_degree {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : (e ! : K) ≠ 0) :
    ∀ k < min n (e + 1),
      ∃ p ∈ Submodule.span K (Set.range fun i => (C w * X + C (β i)) ^ e),
        p.natDegree = e - k ∧ p.leadingCoeff = (e.choose k : K) * w ^ (e - k) := by
  intro k hk
  have ha : (e.choose k : K) * w ^ (e - k) ≠ 0 :=
    mul_ne_zero (choose_cast_ne_zero hfac (by omega)) (pow_ne_zero _ hw)
  obtain ⟨p, hp, hd, hc⟩ := powers_top_cover hw β hβ hfac (e - k) (by omega) (by omega)
    ((e.choose k : K) * w ^ (e - k))
  have hnat : p.natDegree = e - k :=
    le_antisymm hd (le_natDegree_of_ne_zero (by rw [hc]; exact ha))
  exact ⟨p, hp, hnat, by rw [leadingCoeff, hnat, hc]⟩

theorem powers_finrank {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : (e ! : K) ≠ 0) :
    finrank K (Submodule.span K (Set.range fun i => (C w * X + C (β i)) ^ e)) =
      min n (e + 1) := by
  have h := finrank_eq_min_of_sep hw (fun k hk => choose_cast_ne_zero hfac hk)
    (fun i => (C w * X + C (β i)) ^ e) (fun i k => β i ^ k)
    (fun j => by rw [apolar_pow, sub_self, degree_zero]; exact WithBot.bot_lt_coe _)
    (simple_sep β hβ (by simp) (min_le_right _ _))
  simpa using h

/-! ### P2: Hermite (confluent) spans -/

/-- The `L`-form generators `L_i^e`, `L_i · L_i^e`. -/
def hermGen (w : K) (e : ℕ) {n : ℕ} (β : Fin n → K) : Fin n ⊕ Fin n → K[X] :=
  Sum.elim (fun i => (C w * X + C (β i)) ^ e)
    (fun i => (C w * X + C (β i)) * (C w * X + C (β i)) ^ e)

lemma hermGen_sub {w : K} {e n : ℕ} (β : Fin n → K) (he : ((e + 1 : ℕ) : K) ≠ 0)
    (j : Fin n ⊕ Fin n) : hermGen w e β j - apolar w (e + 1) (hermS e β j) = 0 := by
  rcases j with i | i
  · show (C w * X + C (β i)) ^ e -
        apolar w (e + 1) (fun k => ((e + 1 : ℕ) : K)⁻¹ * ((k : K) * β i ^ (k - 1))) = 0
    rw [apolar_pow_pred w (β i) e he, sub_self]
  · show (C w * X + C (β i)) * (C w * X + C (β i)) ^ e -
        apolar w (e + 1) (fun k => β i ^ k) = 0
    rw [apolar_pow, pow_succ', sub_self]

theorem hermite_span_eq {w : K} (hw : w ≠ 0) {e n : ℕ} (β : Fin n → K) :
    Submodule.span K (Set.range (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
        (fun i => X * (C w * X + C (β i)) ^ e))) =
      Submodule.span K (Set.range (hermGen w e β)) :=
  span_X_mul_eq hw β (fun i => (C w * X + C (β i)) ^ e)

lemma hermite_hch {e : ℕ} (hfac : ((e + 1) ! : K) ≠ 0) :
    ∀ k ≤ e + 1, ((e + 1).choose k : K) ≠ 0 := fun _ hk => choose_cast_ne_zero hfac hk

lemma hermite_he {e : ℕ} (hfac : ((e + 1) ! : K) ≠ 0) : ((e + 1 : ℕ) : K) ≠ 0 :=
  natCast_ne_zero_of_factorial hfac (by omega) le_rfl

theorem hermite_top_cover {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : ((e + 1) ! : K) ≠ 0) :
    ∀ D, e + 2 - min (2 * n) (e + 2) ≤ D → D ≤ e + 1 → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
          (fun i => X * (C w * X + C (β i)) ^ e))),
        p.natDegree ≤ D ∧ p.coeff D = a := by
  rw [hermite_span_eq hw β]
  exact top_cover hw (min_le_right _ _) (hermite_hch hfac) (hermGen w e β) (hermS e β)
    (fun j => by rw [hermGen_sub β (hermite_he hfac), degree_zero]; exact WithBot.bot_lt_coe _)
    (hermite_sep β hβ (hermite_he hfac) (min_le_left _ _) (min_le_right _ _))

theorem hermite_span_dim {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : ((e + 1) ! : K) ≠ 0) :
    finrank K (Submodule.span K (Set.range (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
        (fun i => X * (C w * X + C (β i)) ^ e)))) = min (2 * n) (e + 2) := by
  rw [hermite_span_eq hw β]
  have hc : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by simp; omega
  have h := finrank_eq_min_of_sep hw (hermite_hch hfac) (hermGen w e β) (hermS e β)
    (fun j => by rw [hermGen_sub β (hermite_he hfac), degree_zero]; exact WithBot.bot_lt_coe _)
    (hermite_sep β hβ (hermite_he hfac) (by rw [hc]; exact min_le_left _ _) (min_le_right _ _))
  rw [h, hc]

theorem hermite_linearIndependent {n e : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : ((e + 1) ! : K) ≠ 0) (hn : 2 * n ≤ e + 2) :
    LinearIndependent K (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
        (fun i => X * (C w * X + C (β i)) ^ e)) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have h := hermite_span_dim hw β hβ hfac
  rw [min_eq_left hn] at h
  have hc : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by simp; omega
  rw [hc]
  exact h.symm

/-! ### P3a: the G factor `1 + L^m` -/

lemma gfactor_sub {w b : K} (m : ℕ) :
    (1 + (C w * X + C b) ^ m) -
      apolar w m (fun k => b ^ k + if k = m then 1 else 0) = 0 := by
  rw [apolar_add, apolar_pow, apolar_indicator]
  ring

lemma gfactor_sep {n m r : ℕ} (hm : 1 ≤ m) (β : Fin n → K) (hβ : Function.Injective β)
    (hr1 : r ≤ n) (hr2 : r ≤ m + 1) :
    ∀ q : K[X], q.degree < r →
      (∀ j, pair m q (fun k => β j ^ k + if k = m then 1 else 0) = 0) → q = 0 := by
  intro q hq hj
  rcases eq_or_ne q 0 with h | h
  · exact h
  have hlt := (natDegree_lt_iff_degree_lt h).2 hq
  have hroot : q + C (q.coeff m) = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hβ (fun i => ?_)
      (by rw [natDegree_add_C]; simp; omega)
    have := hj i
    rw [pair_add, pair_pow (by omega), pair_indicator] at this
    rw [eval_add, eval_C]
    exact this
  have hq' : q = -C (q.coeff m) := eq_neg_of_add_eq_zero_left hroot
  have hm0 : q.coeff m = 0 := by
    have h2 := congrArg (fun p : K[X] => p.coeff m) hq'
    simp only [coeff_neg, coeff_C, if_neg (show m ≠ 0 by omega), neg_zero] at h2
    exact h2
  rw [hq', hm0, C_0, neg_zero]

theorem gfactor_top_cover {n m : ℕ} (hm : 1 ≤ m) {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : (m ! : K) ≠ 0) :
    ∀ D, m + 1 - min n (m + 1) ≤ D → D ≤ m → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range fun i => 1 + (C w * X + C (β i)) ^ m),
        p.natDegree ≤ D ∧ p.coeff D = a :=
  top_cover hw (min_le_right _ _) (fun k hk => choose_cast_ne_zero hfac hk) _
    (fun i k => β i ^ k + if k = m then 1 else 0)
    (fun j => by rw [gfactor_sub, degree_zero]; exact WithBot.bot_lt_coe _)
    (gfactor_sep hm β hβ (min_le_left _ _) (min_le_right _ _))

theorem gfactor_span_dim {n m : ℕ} (hm : 1 ≤ m) {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : (m ! : K) ≠ 0) :
    finrank K (Submodule.span K (Set.range fun i => 1 + (C w * X + C (β i)) ^ m)) =
      min n (m + 1) := by
  have h := finrank_eq_min_of_sep hw (fun k hk => choose_cast_ne_zero hfac hk)
    (fun i => 1 + (C w * X + C (β i)) ^ m) (fun i k => β i ^ k + if k = m then 1 else 0)
    (fun j => by rw [gfactor_sub, degree_zero]; exact WithBot.bot_lt_coe _)
    (gfactor_sep hm β hβ (by simp) (min_le_right _ _))
  simpa using h

/-! ### P3b: `{Φ, X·Φ}` for `Φ = 1 + L^m`, degrees ≥ 2 only -/

/-- `L`-form generators `Φ_i`, `L_i · Φ_i`. -/
def gHermGen (w : K) (m : ℕ) {n : ℕ} (β : Fin n → K) : Fin n ⊕ Fin n → K[X] :=
  Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ m)
    (fun i => (C w * X + C (β i)) * (1 + (C w * X + C (β i)) ^ m))

lemma gHermGen_sub_degree {w : K} {m n r : ℕ} (β : Fin n → K) (he : ((m + 1 : ℕ) : K) ≠ 0)
    (hr : r ≤ m) (j : Fin n ⊕ Fin n) :
    (gHermGen w m β j - apolar w (m + 1) (hermS m β j)).degree <
      ((m + 1 + 1 - r : ℕ) : WithBot ℕ) := by
  rcases j with i | i
  · show (1 + (C w * X + C (β i)) ^ m -
        apolar w (m + 1) (fun k => ((m + 1 : ℕ) : K)⁻¹ * ((k : K) * β i ^ (k - 1)))).degree < _
    rw [apolar_pow_pred w (β i) m he, add_sub_cancel_right, degree_one]
    exact_mod_cast (show 0 < m + 1 + 1 - r by omega)
  · show ((C w * X + C (β i)) * (1 + (C w * X + C (β i)) ^ m) -
        apolar w (m + 1) (fun k => β i ^ k)).degree < _
    rw [apolar_pow]
    have h : (C w * X + C (β i)) * (1 + (C w * X + C (β i)) ^ m) -
        (C w * X + C (β i)) ^ (m + 1) = C w * X + C (β i) := by ring
    rw [h]
    exact lt_of_le_of_lt degree_linear_le (by exact_mod_cast (show 1 < m + 1 + 1 - r by omega))

theorem gfactor_hermite_span_eq {w : K} (hw : w ≠ 0) {m n : ℕ} (β : Fin n → K) :
    Submodule.span K (Set.range (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ m)
        (fun i => X * (1 + (C w * X + C (β i)) ^ m)))) =
      Submodule.span K (Set.range (gHermGen w m β)) :=
  span_X_mul_eq hw β (fun i => 1 + (C w * X + C (β i)) ^ m)

theorem gfactor_hermite_top_cover {n m : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : ((m + 1) ! : K) ≠ 0) :
    ∀ D, m + 2 - min (2 * n) m ≤ D → D ≤ m + 1 → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ m)
          (fun i => X * (1 + (C w * X + C (β i)) ^ m)))),
        p.natDegree ≤ D ∧ p.coeff D = a := by
  rw [gfactor_hermite_span_eq hw β]
  exact top_cover hw (by omega) (hermite_hch hfac) (gHermGen w m β) (hermS m β)
    (gHermGen_sub_degree β (hermite_he hfac) (min_le_right _ _))
    (hermite_sep β hβ (hermite_he hfac) (min_le_left _ _) (by omega))

theorem gfactor_hermite_linearIndependent {n m : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) (hfac : ((m + 1) ! : K) ≠ 0) (hn : 2 * n ≤ m) :
    LinearIndependent K (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ m)
        (fun i => X * (1 + (C w * X + C (β i)) ^ m))) := by
  have hc : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by simp; omega
  have hlo := le_finrank_of_top_cover hw (by omega : 2 * n ≤ m + 1 + 1) (hermite_hch hfac)
    (gHermGen w m β) (hermS m β) (gHermGen_sub_degree β (hermite_he hfac) hn)
    (hermite_sep β hβ (hermite_he hfac) le_rfl (by omega))
  rw [← gfactor_hermite_span_eq hw β] at hlo
  have hup := finrank_range_le_card (R := K) (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ m)
    (fun i => X * (1 + (C w * X + C (β i)) ^ m)))
  rw [linearIndependent_iff_card_eq_finrank_span, hc]
  rw [hc] at hup
  exact le_antisymm hlo hup

/-! ### R0 corollaries: degrees 26 / 28 -/

section R0
variable (hfac : ∀ n ≤ 28, (n ! : K) ≠ 0)
include hfac

theorem divided_difference_degree_R0 {n e : ℕ} (he : e ≤ 26) {w : K} (hw : w ≠ 0)
    (β : Fin n → K) (hβ : Function.Injective β) :
    ∀ k < min n (e + 1),
      ∃ p ∈ Submodule.span K (Set.range fun i => (C w * X + C (β i)) ^ e),
        p.natDegree = e - k ∧ p.leadingCoeff = (e.choose k : K) * w ^ (e - k) :=
  divided_difference_degree hw β hβ (hfac e (by omega))

theorem powers_finrank_R0 {n e : ℕ} (he : e ≤ 26) {w : K} (hw : w ≠ 0)
    (β : Fin n → K) (hβ : Function.Injective β) :
    finrank K (Submodule.span K (Set.range fun i => (C w * X + C (β i)) ^ e)) =
      min n (e + 1) :=
  powers_finrank hw β hβ (hfac e (by omega))

theorem hermite_span_dim_R0 {n e : ℕ} (he : e ≤ 26) {w : K} (hw : w ≠ 0)
    (β : Fin n → K) (hβ : Function.Injective β) :
    finrank K (Submodule.span K (Set.range (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
        (fun i => X * (C w * X + C (β i)) ^ e)))) = min (2 * n) (e + 2) :=
  hermite_span_dim hw β hβ (hfac (e + 1) (by omega))

theorem hermite_top_cover_R0 {n e : ℕ} (he : e ≤ 26) {w : K} (hw : w ≠ 0)
    (β : Fin n → K) (hβ : Function.Injective β) :
    ∀ D, e + 2 - min (2 * n) (e + 2) ≤ D → D ≤ e + 1 → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range (Sum.elim (fun i => (C w * X + C (β i)) ^ e)
          (fun i => X * (C w * X + C (β i)) ^ e))),
        p.natDegree ≤ D ∧ p.coeff D = a :=
  hermite_top_cover hw β hβ (hfac (e + 1) (by omega))

theorem gfactor_span_dim_R0 {n : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) :
    finrank K (Submodule.span K (Set.range fun i => 1 + (C w * X + C (β i)) ^ 26)) =
      min n 27 :=
  gfactor_span_dim (by norm_num) hw β hβ (hfac 26 (by norm_num))

theorem gfactor_top_cover_R0 {n : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) :
    ∀ D, 27 - min n 27 ≤ D → D ≤ 26 → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range fun i => 1 + (C w * X + C (β i)) ^ 26),
        p.natDegree ≤ D ∧ p.coeff D = a :=
  gfactor_top_cover (by norm_num) hw β hβ (hfac 26 (by norm_num))

theorem gfactor_hermite_top_cover_R0 {n : ℕ} {w : K} (hw : w ≠ 0) (β : Fin n → K)
    (hβ : Function.Injective β) :
    ∀ D, 28 - min (2 * n) 26 ≤ D → D ≤ 27 → ∀ a : K,
      ∃ p ∈ Submodule.span K (Set.range (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ 26)
          (fun i => X * (1 + (C w * X + C (β i)) ^ 26)))),
        p.natDegree ≤ D ∧ p.coeff D = a :=
  gfactor_hermite_top_cover hw β hβ (hfac 27 (by norm_num))

theorem gfactor_hermite_linearIndependent_R0 {n : ℕ} (hn : n ≤ 13) {w : K} (hw : w ≠ 0)
    (β : Fin n → K) (hβ : Function.Injective β) :
    LinearIndependent K (Sum.elim (fun i => 1 + (C w * X + C (β i)) ^ 26)
        (fun i => X * (1 + (C w * X + C (β i)) ^ 26))) :=
  gfactor_hermite_linearIndependent hw β hβ (hfac 27 (by norm_num)) (by omega)

end R0

end R0Z.HermiteSpan

#print axioms R0Z.HermiteSpan.coeff_cover
#print axioms R0Z.HermiteSpan.coeff_cover_of_leadingCoeff_span
#print axioms R0Z.HermiteSpan.leading_coeff_cover
#print axioms R0Z.HermiteSpan.leading_coeff_cover_root
#print axioms R0Z.HermiteSpan.top_cover
#print axioms R0Z.HermiteSpan.le_finrank_of_top_cover
#print axioms R0Z.HermiteSpan.finrank_eq_min_of_sep
#print axioms R0Z.HermiteSpan.powers_top_cover
#print axioms R0Z.HermiteSpan.divided_difference_degree
#print axioms R0Z.HermiteSpan.powers_finrank
#print axioms R0Z.HermiteSpan.hermite_span_eq
#print axioms R0Z.HermiteSpan.hermite_top_cover
#print axioms R0Z.HermiteSpan.hermite_span_dim
#print axioms R0Z.HermiteSpan.hermite_linearIndependent
#print axioms R0Z.HermiteSpan.gfactor_top_cover
#print axioms R0Z.HermiteSpan.gfactor_span_dim
#print axioms R0Z.HermiteSpan.gfactor_hermite_top_cover
#print axioms R0Z.HermiteSpan.gfactor_hermite_linearIndependent
#print axioms R0Z.HermiteSpan.divided_difference_degree_R0
#print axioms R0Z.HermiteSpan.powers_finrank_R0
#print axioms R0Z.HermiteSpan.hermite_span_dim_R0
#print axioms R0Z.HermiteSpan.hermite_top_cover_R0
#print axioms R0Z.HermiteSpan.gfactor_span_dim_R0
#print axioms R0Z.HermiteSpan.gfactor_top_cover_R0
#print axioms R0Z.HermiteSpan.gfactor_hermite_top_cover_R0
#print axioms R0Z.HermiteSpan.gfactor_hermite_linearIndependent_R0
