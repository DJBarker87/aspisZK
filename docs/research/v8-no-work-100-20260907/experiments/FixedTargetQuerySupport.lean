import AspisFormal.V5FriConcreteEncoderApplicability
import Mathlib.Data.Finset.Powerset

/-! Research only. Fixed-before-challenge targets, independent finite product
sampling. This is not an adaptive provider coverage or Fiat–Shamir theorem.
All counts remain symbolic: no enumeration of QM31 or the query universe. -/

set_option autoImplicit false

namespace AspisV8.FixedTargetQuerySupport

open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability

variable {K : Type*} [Field K]

noncomputable def foldCoefficients (x y : K) (v : Fin 4 → K) : Fin 4 → K :=
  ![(v 0 + v 1 + v 2 + v 3) / 4,
    (v 0 - v 1 - v 2 + v 3) / (4*y),
    (v 0 + v 1 - v 2 - v 3) / (4*x),
    (v 0 - v 1 + v 2 - v 3) / (4*x*y)]

/-- The actual low-bit circle sign order, not an arbitrary tensor permutation. -/
theorem foldCoefficients_injective (x y : K) (hfour : (4 : K) ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    Function.Injective (foldCoefficients x y) := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [foldCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  have e0 := (div_left_inj' hfour).mp h0
  have e1 := (div_left_inj' (mul_ne_zero hfour hy)).mp h1
  have e2 := (div_left_inj' (mul_ne_zero hfour hx)).mp h2
  have e3 := (div_left_inj' (mul_ne_zero (mul_ne_zero hfour hx) hy)).mp h3
  have z0 : (4 : K) * (v 0 - w 0) = 0 := by linear_combination e0 + e1 + e2 + e3
  have z1 : (4 : K) * (v 1 - w 1) = 0 := by linear_combination e0 - e1 + e2 - e3
  have z2 : (4 : K) * (v 2 - w 2) = 0 := by linear_combination e0 - e1 - e2 + e3
  have z3 : (4 : K) * (v 3 - w 3) = 0 := by linear_combination e0 + e1 - e2 - e3
  funext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp z0).resolve_left hfour)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp z1).resolve_left hfour)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp z2).resolve_left hfour)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp z3).resolve_left hfour)

noncomputable def foldedPolynomial (x y : K) (v : Fin 4 → K) : K[X] :=
  monomialPolynomial (foldCoefficients x y v)

theorem foldedPolynomial_ne_zero (x y : K) (hfour : (4 : K) ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (v : Fin 4 → K) (hv : v ≠ 0) :
    foldedPolynomial x y v ≠ 0 := by
  intro h
  apply hv
  apply foldCoefficients_injective x y hfour hx hy
  apply monomialPolynomial_injective
  have hz : foldCoefficients x y (0 : Fin 4 → K) = 0 := by
    funext i
    fin_cases i <;> simp [foldCoefficients]
  rw [hz]
  simpa [foldedPolynomial, monomialPolynomial] using h

theorem foldedPolynomial_degree (x y : K) (v : Fin 4 → K) :
    (foldedPolynomial x y v).natDegree ≤ 3 :=
  monomialPolynomial_natDegree_le (by decide) _

/-- Literal two-step fold, including the negative-y orientation of slots 2,3. -/
theorem foldedPolynomial_eval_literal (x y a : K) (v : Fin 4 → K)
    (hfour : (4 : K) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    (foldedPolynomial x y v).eval a =
      (((v 0 + v 1)/2 + a*(v 0-v 1)/(2*y)) +
        ((v 2+v 3)/2 - a*(v 2-v 3)/(2*y)))/2 +
      a^2 * (((v 0+v 1)/2 + a*(v 0-v 1)/(2*y)) -
        ((v 2+v 3)/2 - a*(v 2-v 3)/(2*y)))/(2*x) := by
  have htwo : (2 : K) ≠ 0 := by
    intro h
    apply hfour
    calc (4 : K) = 2*2 := by ring
         _ = 0 := by rw [h]; simp
  simp [foldedPolynomial, monomialPolynomial, Fin.sum_univ_succ, foldCoefficients]
  field_simp
  ring

/-- Nonzero denominators preserve a nonzero selected residual slot. -/
theorem divided_residual_ne_zero (r den : Fin 4 → K) (j : Fin 4)
    (hr : r j ≠ 0) (hd : den j ≠ 0) :
    (fun i => r i / den i) ≠ 0 := by
  intro h
  exact div_ne_zero hr hd (congrFun h j)

section Counting
variable [DecidableEq K]

theorem root_filter_card_le (S : Finset K) (p : K[X]) (hp : p ≠ 0)
    (d : ℕ) (hd : p.natDegree ≤ d) :
    (S.filter fun a => p.eval a = 0).card ≤ d := by
  apply (Polynomial.card_le_degree_of_subset_roots (p := p) ?_).trans hd
  intro a ha
  exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp ha).2

/-- Exact two-stage numerator. R is fixed before gamma; F gamma is fixed
before alpha. It may depend on gamma, but is nonzero whenever R gamma is.
Gamma and alpha range over arbitrary explicit finite sets G and A. -/
theorem two_stage_count (G A : Finset K) (R : K[X]) (F : K → K[X])
    (d t : ℕ) (hR : R ≠ 0) (hdeg : R.natDegree ≤ d)
    (hd : d ≤ G.card) (ht : t ≤ A.card)
    (hF : ∀ g ∈ G, R.eval g ≠ 0 → F g ≠ 0)
    (hFdeg : ∀ g ∈ G, (F g).natDegree ≤ t) :
    (∑ g ∈ G, (A.filter fun a => (F g).eval a = 0).card)
      ≤ d * A.card + (G.card - d) * t := by
  classical
  let B := G.filter fun g => R.eval g = 0
  have hb : B.card ≤ d := root_filter_card_le G R hR d hdeg
  have part := Finset.card_filter_add_card_filter_not (s := G) (p := fun g => R.eval g = 0)
  have bounded : (∑ g ∈ G, (A.filter fun a => (F g).eval a = 0).card)
      ≤ B.card * A.card + (G.card - B.card) * t := by
    calc
      _ ≤ ∑ g ∈ G, if R.eval g = 0 then A.card else t := by
        apply Finset.sum_le_sum
        intro g hg
        split_ifs with hz
        · exact Finset.card_filter_le _ _
        · exact root_filter_card_le A (F g) (hF g hg hz) t (hFdeg g hg)
      _ = B.card * A.card + (G.card - B.card) * t := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const, smul_eq_mul]
        dsimp [B] at *
        congr 1
        congr 1
        omega
  have hbg : B.card ≤ G.card := hb.trans hd
  have eqb := Nat.sub_add_cancel hbg
  have eqd := Nat.sub_add_cancel hd
  have monotone := Nat.mul_le_mul_right (A.card - t) hb
  have eqt := Nat.sub_add_cancel ht
  nlinarith

/-- The all-common schedules are counted exactly by binomial coefficients. -/
theorem common_schedule_card {I : Type*} [DecidableEq I]
    (U C : Finset I) (hC : C ⊆ U) (q : ℕ) :
    ((U.powersetCard q).filter fun S => S ⊆ C).card = C.card.choose q := by
  have heq : (U.powersetCard q).filter (fun S => S ⊆ C) = C.powersetCard q := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, hq⟩, hs⟩
      exact ⟨hs, hq⟩
    · rintro ⟨hs, hq⟩
      exact ⟨⟨hs.trans hC, hq⟩, hs⟩
  rw [heq, Finset.card_powersetCard]

/-- Count accepted wrong-support triples, without a union over locations.
The per-schedule bound is consumed once for each bad schedule. -/
theorem wrong_support_count {I : Type*} [DecidableEq I]
    (U C : Finset I) (hC : C ⊆ U) (q cap : ℕ)
    (acceptedPairs : Finset I → ℕ)
    (hcap : ∀ S ∈ U.powersetCard q, ¬ S ⊆ C → acceptedPairs S ≤ cap) :
    (∑ S ∈ (U.powersetCard q).filter (fun S => ¬ S ⊆ C), acceptedPairs S)
      ≤ (U.card.choose q - C.card.choose q) * cap := by
  classical
  have part := Finset.card_filter_add_card_filter_not
    (s := U.powersetCard q) (p := fun S => S ⊆ C)
  rw [common_schedule_card U C hC q, Finset.card_powersetCard] at part
  calc
    _ ≤ ∑ _S ∈ (U.powersetCard q).filter (fun S => ¬ S ⊆ C), cap := by
      apply Finset.sum_le_sum
      intro S hS
      exact hcap S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
    _ = _ := by
      simp only [Finset.sum_const, smul_eq_mul]
      congr 1
      omega

noncomputable def fibreFold {I : Type*} (x y : I → K)
    (den : I → Fin 4 → K) (R : I → Fin 4 → K[X]) (i : I) (g : K) : K[X] :=
  foldedPolynomial (x i) (y i) (fun j => (R i j).eval g / den i j)

/-- All pointwise checks; neither the target nor its component residual
polynomials can depend on gamma, alpha or the schedule in this definition. -/
noncomputable def pointwisePairCount {I : Type*} (G A : Finset K)
    (x y : I → K) (den : I → Fin 4 → K) (R : I → Fin 4 → K[X])
    (S : Finset I) : ℕ := by
  classical
  exact ∑ g ∈ G, (A.filter fun a => ∀ i ∈ S, (fibreFold x y den R i g).eval a = 0).card

/-- One deterministically selected bad fibre suffices. The witness can depend
on S but not on either challenge. No union over fibres or query positions. -/
theorem pointwise_bad_schedule_count {I : Type*} [DecidableEq I]
    (G A : Finset K) (x y : I → K) (den : I → Fin 4 → K)
    (R : I → Fin 4 → K[X]) (S : Finset I) (i : I) (hi : i ∈ S) (j : Fin 4)
    (d : ℕ) (hd : d ≤ G.card) (ht : 3 ≤ A.card)
    (hR : R i j ≠ 0) (hdeg : (R i j).natDegree ≤ d)
    (hfour : (4 : K) ≠ 0) (hx : x i ≠ 0) (hy : y i ≠ 0)
    (hden : den i j ≠ 0) :
    pointwisePairCount G A x y den R S ≤ d*A.card + (G.card-d)*3 := by
  classical
  calc
    _ ≤ ∑ g ∈ G, (A.filter fun a => (fibreFold x y den R i g).eval a = 0).card := by
      apply Finset.sum_le_sum
      intro g _hg
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
        (Finset.mem_filter.mp ha).2 i hi⟩
    _ ≤ _ := by
      apply two_stage_count G A (R i j) (fibreFold x y den R i) d 3 hR hdeg hd ht
      · intro g _hg hne
        apply foldedPolynomial_ne_zero _ _ hfour hx hy
        exact divided_residual_ne_zero _ _ j hne hden
      · intro g _hg
        exact foldedPolynomial_degree _ _ _

/-- Integrated fixed-target theorem, as an exact numerator bound for the
uniform product of nonzero-gamma/full-alpha sets and direct q-subsets.
C is precisely the set of identically matching component fibres.
This theorem constructs its bad-fibre witness; it assumes no provider member. -/
theorem fixed_target_wrong_support_count {I : Type*} [DecidableEq I]
    (U C : Finset I) (hC : C ⊆ U) (q : ℕ)
    (G A : Finset K) (x y : I → K) (den : I → Fin 4 → K)
    (R : I → Fin 4 → K[X]) (d : ℕ) (hd : d ≤ G.card) (ht : 3 ≤ A.card)
    (hfour : (4 : K) ≠ 0)
    (hxy : ∀ i ∈ U, x i ≠ 0 ∧ y i ≠ 0)
    (hden : ∀ i ∈ U, ∀ j, den i j ≠ 0)
    (hdeg : ∀ i ∈ U, ∀ j, (R i j).natDegree ≤ d)
    (hcommon : ∀ i ∈ U, i ∈ C ↔ ∀ j, R i j = 0) :
    (∑ S ∈ (U.powersetCard q).filter (fun S => ¬ S ⊆ C),
      pointwisePairCount G A x y den R S)
      ≤ (U.card.choose q - C.card.choose q) * (d*A.card + (G.card-d)*3) := by
  classical
  apply wrong_support_count U C hC q _ _
  intro S hS hbad
  obtain ⟨i, hi, hnot⟩ := Finset.not_subset.mp hbad
  have hiU := (Finset.mem_powersetCard.mp hS).1 hi
  have hex : ∃ j, R i j ≠ 0 := by
    by_contra hn
    apply hnot
    apply (hcommon i hiU).mpr
    simpa only [not_exists, not_not] using hn
  obtain ⟨j, hj⟩ := hex
  exact pointwise_bad_schedule_count G A x y den R S i hi j d hd ht hj
    (hdeg i hiU j) hfour (hxy i hiU).1 (hxy i hiU).2 (hden i hiU j)

/-- A generic total-count composition: common schedules cost at most all
challenge pairs, and wrong-support schedules retain their proved joint bound. -/
theorem total_count_from_wrong_support {I : Type*} [DecidableEq I]
    (U C : Finset I) (hC : C ⊆ U) (q pairs badBound : ℕ)
    (count : Finset I → ℕ)
    (htrivial : ∀ S ∈ U.powersetCard q, count S ≤ pairs)
    (hbad : (∑ S ∈ (U.powersetCard q).filter (fun S => ¬ S ⊆ C), count S) ≤ badBound) :
    (∑ S ∈ U.powersetCard q, count S) ≤ C.card.choose q * pairs + badBound := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (U.powersetCard q) (fun S => S ⊆ C) count]
  apply Nat.add_le_add _ hbad
  calc
    _ ≤ ∑ _S ∈ (U.powersetCard q).filter (fun S => S ⊆ C), pairs := by
      apply Finset.sum_le_sum
      intro S hS
      exact htrivial S (Finset.mem_filter.mp hS).1
    _ = _ := by simp [common_schedule_card U C hC q]

theorem pointwisePairCount_le {I : Type*} (G A : Finset K)
    (x y : I → K) (den : I → Fin 4 → K) (R : I → Fin 4 → K[X])
    (S : Finset I) : pointwisePairCount G A x y den R S ≤ G.card*A.card := by
  classical
  calc
    _ ≤ ∑ _g ∈ G, A.card := Finset.sum_le_sum (fun _ _ => Finset.card_filter_le _ _)
    _ = _ := by simp

/-- The normalization is an identity in rationals, not a floating estimate. -/
theorem normalize_wrong_support (total common g a d t : ℕ)
    (hc : common ≤ total) (hd : d ≤ g)
    (htotal : total ≠ 0) (hg : g ≠ 0) (ha : a ≠ 0) :
    (((total-common) * (d*a + (g-d)*t) : ℕ) : ℚ) / (total*g*a) =
      (1 - (common : ℚ)/total) *
        ((d : ℚ)/g + (1-(d : ℚ)/g)*(t : ℚ)/a) := by
  have htotal' : (total : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr htotal
  have hg' : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  push_cast [Nat.cast_sub hc, Nat.cast_sub hd]
  field_simp

/-! ## The fixed-zero disjoint-root counterexample family

The probability theorem below needs no disjointness assumption: it handles
every root-product family of the given size. Disjointness is used separately
to count the exceptional gammas of the rejected same-support claim. -/

noncomputable def zeroExampleResidual {I : Type*} [DecidableEq I]
    (common : Finset I) (roots : I → Finset K) (i : I) (_j : Fin 4) : K[X] :=
  if i ∈ common then 0 else ∏ r ∈ roots i, (X - C r)

omit [DecidableEq K] in
theorem zeroExample_common_iff {I : Type*} [DecidableEq I]
    (common : Finset I) (roots : I → Finset K) (i : I) :
    i ∈ common ↔ ∀ j, zeroExampleResidual common roots i j = 0 := by
  classical
  by_cases hi : i ∈ common
  · simp [zeroExampleResidual, hi]
  · have hn := (Polynomial.monic_prod_X_sub_C (fun r : K => r) (roots i)).ne_zero
    simp [zeroExampleResidual, hi, hn]

/-- Explicitly instantiate the reference target as zero in all four slots.
The polynomials are the actual root products, not an assumed recovered tuple. -/
theorem zeroExample_wrong_support_count {I : Type*} [DecidableEq I]
    (U common : Finset I) (hC : common ⊆ U) (q : ℕ)
    (G A : Finset K) (x y : I → K) (den : I → Fin 4 → K)
    (roots : I → Finset K) (d : ℕ) (hd : d ≤ G.card) (ht : 3 ≤ A.card)
    (hfour : (4 : K) ≠ 0) (hxy : ∀ i ∈ U, x i ≠ 0 ∧ y i ≠ 0)
    (hden : ∀ i ∈ U, ∀ j, den i j ≠ 0)
    (hroots : ∀ i ∈ U, (roots i).card ≤ d) :
    (∑ S ∈ (U.powersetCard q).filter (fun S => ¬ S ⊆ common),
      pointwisePairCount G A x y den (zeroExampleResidual common roots) S)
      ≤ (U.card.choose q - common.card.choose q) * (d*A.card + (G.card-d)*3) := by
  classical
  apply fixed_target_wrong_support_count U common hC q G A x y den _ d hd ht hfour hxy hden
  · intro i hi j
    by_cases hc : i ∈ common
    · simp [zeroExampleResidual, hc]
    · simpa [zeroExampleResidual, hc] using hroots i hi
  · intro i _hi
    exact zeroExample_common_iff common roots i

omit [DecidableEq K] in
theorem zeroExample_top_coefficient {I : Type*} [DecidableEq I]
    (common : Finset I) (roots : I → Finset K) (i : I) (hi : i ∉ common)
    (j : Fin 4) :
    (zeroExampleResidual common roots i j).coeff (roots i).card = 1 := by
  classical
  have hm := Polynomial.monic_prod_X_sub_C (fun r : K => r) (roots i)
  have hc := hm.leadingCoeff
  simpa [zeroExampleResidual, hi, Polynomial.leadingCoeff] using hc

omit [Field K] in
theorem disjoint_exceptional_gamma_card {I : Type*} [DecidableEq I]
    (U common : Finset I) (hC : common ⊆ U) (roots : I → Finset K) (d : ℕ)
    (hdisjoint : (↑(U \ common) : Set I).PairwiseDisjoint roots)
    (hsize : ∀ i ∈ U \ common, (roots i).card = d) :
    ((U \ common).biUnion roots).card = d*(U.card-common.card) := by
  classical
  rw [Finset.card_biUnion hdisjoint]
  simp_rw [Finset.sum_congr rfl hsize]
  simp [Finset.card_sdiff_of_subset hC, Nat.mul_comm]

/-- Symbolic obstruction used by the old counterexample: zero on more than
the encoder's root cap forces the zero message, which cannot also equal one
at the extra symbol. The encoder/root-cap and index-map bridge stay explicit. -/
theorem same_support_recovery_impossible {I M : Type*} [Zero M]
    (commonSymbols : Finset I) (extra : I) (encode : M → I → K) (cap : ℕ)
    (hzero : ∀ i, encode 0 i = 0)
    (hcap : ∀ m, m ≠ 0 →
      (commonSymbols.filter fun i => encode m i = 0).card ≤ cap)
    (hlarge : cap < commonSymbols.card) :
    ¬ ∃ m, (∀ i ∈ commonSymbols, encode m i = 0) ∧ encode m extra = 1 := by
  classical
  rintro ⟨m, hm, hextra⟩
  have hmzero : m = 0 := by
    by_contra hn
    have hf : commonSymbols.filter (fun i => encode m i = 0) = commonSymbols :=
      Finset.filter_eq_self.mpr hm
    have hb := hcap m hn
    rw [hf] at hb
    omega
  rw [hmzero, hzero] at hextra
  exact zero_ne_one hextra

/-- Sparse symbolic interval proof: no construction of seven million roots. -/
theorem root_label_injective :
    Function.Injective (fun p : ℕ × Fin 28 => 28*p.1+p.2.val+1) := by
  rintro ⟨s, r⟩ ⟨t, u⟩ h
  dsimp only at h
  have hs : s = t := by omega
  have hr : r = u := Fin.ext (by omega)
  exact Prod.ext hs hr

theorem root_label_range (s : Fin 252587) (r : Fin 28) :
    0 < 28*s.val+r.val+1 ∧ 28*s.val+r.val+1 ≤ 7072436 ∧
      28*s.val+r.val+1 < 2147483647 := by
  omega

end Counting

/-- Generalized Tag-73 discrepancy, including its prior constant term. -/
noncomputable def shiftedBatch {q : ℕ} (prior : K) (residual : Fin q → K) : K[X] :=
  C prior - X * monomialPolynomial residual

theorem shiftedBatch_ne_zero {q : ℕ} (prior : K) (r : Fin q → K)
    (hr : r ≠ 0) : shiftedBatch prior r ≠ 0 := by
  intro h
  have heq : C prior = X * monomialPolynomial r := sub_eq_zero.mp h
  have hp : prior = 0 := by
    have hc := congrArg (fun p : K[X] => p.coeff 0) heq
    simpa using hc
  have hm : monomialPolynomial r ≠ 0 := by
    intro hz
    apply hr
    apply monomialPolynomial_injective
    simpa [monomialPolynomial] using hz
  exact (mul_ne_zero X_ne_zero hm) (by rw [← heq, hp]; simp)

theorem shiftedBatch_degree {q : ℕ} (hq : 0 < q) (prior : K) (r : Fin q → K) :
    (shiftedBatch prior r).natDegree ≤ q := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_mul_le.trans
    have hd := monomialPolynomial_natDegree_le hq r
    simp only [Polynomial.natDegree_X]
    omega

theorem shiftedBatch_root_count [DecidableEq K] {q : ℕ} (hq : 0 < q)
    (prior : K) (r : Fin q → K) (hr : r ≠ 0) (nonzeroChallenges : Finset K) :
    (nonzeroChallenges.filter fun rho => (shiftedBatch prior r).eval rho = 0).card ≤ q :=
  root_filter_card_le _ _ (shiftedBatch_ne_zero prior r hr) q (shiftedBatch_degree hq prior r)

#print axioms foldCoefficients_injective
#print axioms foldedPolynomial_ne_zero
#print axioms foldedPolynomial_eval_literal
#print axioms two_stage_count
#print axioms common_schedule_card
#print axioms wrong_support_count
#print axioms fixed_target_wrong_support_count
#print axioms normalize_wrong_support
#print axioms total_count_from_wrong_support
#print axioms pointwisePairCount_le
#print axioms zeroExample_wrong_support_count
#print axioms zeroExample_top_coefficient
#print axioms disjoint_exceptional_gamma_card
#print axioms same_support_recovery_impossible
#print axioms root_label_injective
#print axioms root_label_range
#print axioms shiftedBatch_root_count

end AspisV8.FixedTargetQuerySupport
