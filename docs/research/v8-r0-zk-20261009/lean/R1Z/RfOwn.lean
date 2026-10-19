import R1Z.RfSrc
import R0Z.SilentReduction

/-! D49.4 C2: RF-own, the K-valued closed forms (zf1/DESIGN-P-CERT.txt §2.3), Lean side.

The checker's own column of a source (z4/probe.rs:2207-2254 `raw_c`, reused by
z9.rs:1003-1027 `Lanes::raw/bal` and z9c.rs:224-233 `lift_src`) lists, for a
lane word `e_r` (balanced: minus `e_d` when `r` is copy-inactive), the values
* claims `eq(points(α)[j], r)` (probe.rs:85-107),
* extra `h_weight(α, π r)` (probe.rs:2198-2206),
* OOD `evalrow(π r, z_j)` (probe.rs:114-121; `natural` = basis.rs:22-35),
* opened `evalrow(π r, stored_point(child_index(u, s)))` for the queries.

Here each is defined as a Lean function citing that Rust, and proved equal to
the corresponding cell of `ownMap` (claims `claimsLinear`, extra
`extraLinear`, OOD `oodLinear`, opened `exactInitialLinear`), for every mask
tape whose pure trace is one balanced word in one lane (`ownMap_of_lane`), and
in particular for the checker's sources `maskOnlySrc`, `gSrc`, `dSrc`.

Rust ↔ Lean identifications left to C3: the transport table is `π`
(`row_to_coefficient[r] = π r`), `natural` computes `naturalLineValue`,
`stored_point(child_index(u,s))` is `storedInitialCirclePoint20 (childIndex u s)`.
The F-limb assembly `ιo` of these K-values (four tower limbs for claims, extra
and OOD; one base limb for opened) is not done here. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfOwn

open scoped BigOperators
open R0P R0P.SemSource R0Z.MaskLayout R0Z.HonestView R0Z.Partition R0Z.D12 Polynomial
open AspisR0.Opening AspisR0.ChordGeometry AspisR0.PolynomialPair
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open AspisCircleTensorBinding
open R1Z.RfSrc

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### Sums against the balanced word -/

theorem sum_mul_balWord (f : Fin 1024 → K) (d r : Fin 1024) (hr : r ≠ d) (x : K) :
    ∑ s, f s * balWord d r x s =
      x * f r - (if r ∈ copyInactiveRows then x * f d else 0) := by
  have e : ∀ s, f s * balWord d r x s =
      (if s = r then f r * x else 0) +
        (if s = d then (if r ∈ copyInactiveRows then -(f d * x) else 0) else 0) := by
    intro s
    unfold balWord
    by_cases h1 : s = r
    · have h2 : ¬ s = d := fun h => hr (h1.symm.trans h)
      rw [if_pos h1, if_pos h1, if_neg h2, h1, add_zero]
    · by_cases h2 : s = d
      · rw [if_neg h1, if_neg h1, zero_add, if_pos h2]
        by_cases hm : r ∈ copyInactiveRows
        · rw [if_pos ⟨h2, hm⟩, if_pos hm, h2, mul_neg]
        · rw [if_neg (fun h => hm h.2), if_neg hm, mul_zero]
      · rw [if_neg h1, if_neg h1, if_neg (fun h => h2 h.1), if_neg h2, mul_zero, add_zero]
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> ring

/-- The unit message at coefficient `co`. -/
def unitMsg (co : Fin 1024) : InitialMessage K := fun i => if i = co then 1 else 0

theorem functional_eq_sum (φ : InitialMessage K →ₗ[K] K) (m : InitialMessage K) :
    φ m = ∑ i, m i * φ (unitMsg i) := by
  have hm : m = ∑ i, m i • unitMsg i := by
    funext j
    simp [unitMsg, Finset.sum_apply]
  conv_lhs => rw [hm]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem functional_balWord (φ : InitialMessage K →ₗ[K] K) (π : Fin 1024 ≃ Fin 1024)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) :
    φ (fun i => balWord d r x (π.symm i)) =
      x * φ (unitMsg (π r)) - (if r ∈ copyInactiveRows then x * φ (unitMsg (π d)) else 0) := by
  rw [functional_eq_sum, ← Equiv.sum_comp π]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl (fun s _ => mul_comm _ _)]
  exact sum_mul_balWord (fun s => φ (unitMsg (π s))) d r hr x

/-! ### Claims (`eq`, `points`) -/

/-- Rust `eq(a, r)` (probe.rs:85-93): `∏_i (bit (9−i) of r ? a_i : 1 − a_i)`. -/
def rustEq (p : Fin 10 → K) (r : Fin 1024) : K :=
  ∏ i : Fin 10, if r.val / 2 ^ (9 - i.val) % 2 = 1 then p i else 1 - p i

/-- The coordinate reversal `i ↦ 9 − i` of `Fin 10`. -/
def rev10 : Fin 10 ≃ Fin 10 where
  toFun i := ⟨9 - i.val, by omega⟩
  invFun i := ⟨9 - i.val, by omega⟩
  left_inv i := Fin.ext (show 9 - (9 - i.val) = i.val by have := i.isLt; omega)
  right_inv i := Fin.ext (show 9 - (9 - i.val) = i.val by have := i.isLt; omega)

theorem rustEq_eq (p : Fin 10 → K) (r : Fin 1024) : rustEq p r = eqWeight (toR0 p) r := by
  unfold rustEq eqWeight toR0
  refine Fintype.prod_equiv rev10 _ _ (fun i => ?_)
  have hi := i.isLt
  have e1 : (rev10 i).val = 9 - i.val := rfl
  have e3 : (⟨9 - (rev10 i).val, by omega⟩ : Fin 10) = i :=
    Fin.ext (show 9 - (9 - i.val) = i.val by omega)
  rw [e3, e1]
  rcases Nat.mod_two_eq_zero_or_one (r.val / 2 ^ (9 - i.val)) with h | h
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos h, if_neg (by omega)]

/-- Rust `points(a)` (probe.rs:94-107): `a`, its successor point (the carry
loop is `SemSource.succCarry`), and `a` with coordinates 6, 7 toggled. -/
def rustPoints (a : Fin 10 → K) : Fin 3 → Fin 10 → K
  | 0 => a
  | 1 => successorPoint a
  | 2 => xor12Point a

theorem openingPoints_eq (a : Fin 10 → K) (j : Fin 3) :
    openingPoints a j = toR0 (rustPoints a j) := by
  fin_cases j <;> rfl

theorem claimsLinear_sum (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) (t : Trace K) :
    claimsLinear a j c t = ∑ s, eqWeight (openingPoints a j) s * t c s := by
  simp only [claimsLinear, dotLinear, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem claim_balWord (a : Fin 10 → K) (j : Fin 3) (c : Fin 29) (t : Trace K)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) (ht : t c = balWord d r x) :
    claimsLinear a j c t = x * rustEq (rustPoints a j) r -
      (if r ∈ copyInactiveRows then x * rustEq (rustPoints a j) d else 0) := by
  rw [claimsLinear_sum, ht, sum_mul_balWord _ d r hr, openingPoints_eq, rustEq_eq, rustEq_eq]

/-! ### Extra claim (`h_weight`) -/

/-- Rust `h_weight(a, co)` (probe.rs:2198-2206). -/
def rustHWeight (a : Fin 10 → K) (co : Fin 1024) : K :=
  if co.val < 28 then a 8 ^ co.val else if co.val < 56 then a 9 ^ (co.val - 28) else 0

theorem rustHWeight_eq (a : Fin 10 → K) (co : Fin 1024) : rustHWeight a co = libraWeight a co :=
  rfl

theorem extraLinear_sum (π : Fin 1024 ≃ Fin 1024) (a : Fin 10 → K) (c : Fin 29) (t : Trace K) :
    extraLinear π a c t = ∑ i, libraWeight a i * t c (π.symm i) := by
  simp only [extraLinear, dotLinear, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, coeffsLinear_apply]

theorem extra_balWord (π : Fin 1024 ≃ Fin 1024) (a : Fin 10 → K) (c : Fin 29) (t : Trace K)
    (d r : Fin 1024) (hr : r ≠ d) (x : K) (ht : t c = balWord d r x) :
    extraLinear π a c t = x * rustHWeight a (π r) -
      (if r ∈ copyInactiveRows then x * rustHWeight a (π d) else 0) := by
  rw [extraLinear_sum, ht, ← Equiv.sum_comp π]
  simp only [Equiv.symm_apply_apply]
  rw [sum_mul_balWord (fun s => libraWeight a (π s)) d r hr x]
  rfl

/-! ### OOD and opened (`evalrow`, `natural`) -/

/-- Rust `evalrow(co, (x, y))` (probe.rs:114-121) with `natural` (basis.rs:22-35)
modelled by `naturalLineValue`. -/
def rustEvalRow (co : Fin 1024) (x y : K) : K :=
  if co.val % 2 = 0 then naturalLineValue x (co.val / 2) else naturalLineValue x (co.val / 2) * y

theorem eval_even_unit (co : Fin 1024) (x : K) :
    (initialP0 (unitMsg (K := K) co)).eval x =
      if co.val % 2 = 0 then naturalLineValue x (co.val / 2) else 0 := by
  unfold initialP0
  rw [naturalCoefficientPolynomial_eq_basisSum (by decide), Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, evenCoefficients, unitMsg]
  split_ifs with hc
  · rw [Finset.sum_eq_single (⟨co.val / 2, by omega⟩ : Fin 512)]
    · rw [if_pos (Fin.ext (show (2 * (co.val / 2)) = co.val by omega)), one_mul,
        naturalLineValue_eq_eval]
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (show b.val = co.val / 2 by
          have h2 := congrArg Fin.val h
          simp only at h2
          omega)) hb
      · exact zero_mul _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero (fun b _ => ?_)
    split_ifs with h
    · exact absurd (by
        have h2 := congrArg Fin.val h
        simp only at h2
        omega) hc
    · exact zero_mul _

theorem eval_odd_unit (co : Fin 1024) (x : K) :
    (initialP1 (unitMsg (K := K) co)).eval x =
      if co.val % 2 = 1 then naturalLineValue x (co.val / 2) else 0 := by
  unfold initialP1
  rw [naturalCoefficientPolynomial_eq_basisSum (by decide), Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, oddCoefficients, unitMsg]
  split_ifs with hc
  · rw [Finset.sum_eq_single (⟨co.val / 2, by omega⟩ : Fin 512)]
    · rw [if_pos (Fin.ext (show (2 * (co.val / 2) + 1) = co.val by omega)), one_mul,
        naturalLineValue_eq_eval]
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (show b.val = co.val / 2 by
          have h2 := congrArg Fin.val h
          simp only at h2
          omega)) hb
      · exact zero_mul _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero (fun b _ => ?_)
    split_ifs with h
    · exact absurd (by
        have h2 := congrArg Fin.val h
        simp only at h2
        omega) hc
    · exact zero_mul _

theorem encoderPair_unit (co : Fin 1024) (x y : K) :
    (initialP0 (unitMsg (K := K) co)).eval x + y * (initialP1 (unitMsg (K := K) co)).eval x =
      rustEvalRow co x y := by
  rw [eval_even_unit, eval_odd_unit]
  unfold rustEvalRow
  rcases Nat.mod_two_eq_zero_or_one co.val with h | h
  · rw [if_pos h, if_neg (by omega), if_pos h]
    ring
  · rw [if_neg (by omega), if_pos h, if_neg (by omega)]
    ring

theorem oodLinear_unit (z : Point K) (co : Fin 1024) :
    oodLinear z (unitMsg co) = rustEvalRow co z.1.1 z.1.2 := by
  rw [← encoderPair_unit]
  simp only [oodLinear, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Polynomial.leval_apply, p0Linear_apply, p1Linear_apply, smul_eq_mul]

/-- The stored circle point of an initial-word index, embedded in `K`. -/
def storedX (idx : Fin 1048576) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (AspisCircleGroupOrder.X (AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 idx))

def storedY (idx : Fin 1048576) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (AspisV7ExactOneFoldDomains.storedInitialCirclePoint20 idx).1.2

theorem encoder_unit (co : Fin 1024) (idx : Fin 1048576) :
    exactInitialLinear (unitMsg (K := K) co) idx = rustEvalRow co (storedX idx) (storedY idx) := by
  rw [← encoderPair_unit]
  rfl

/-! ### The own cells of `L` -/

section Cells

variable {Bat : Type} [BatchedLayer K Bat]

theorem ownProj_pointClaim (v : Payload K Bat) (j : Fin 3) (c : Fin 29) :
    R0Z.SilentReduction.ownProj (F := F) v (.pointClaim j c) = v (.pointClaim j c) := rfl
theorem ownProj_extraClaim (v : Payload K Bat) (c : Fin 29) :
    R0Z.SilentReduction.ownProj (F := F) v (.extraClaim c) = v (.extraClaim c) := rfl
theorem ownProj_ood (v : Payload K Bat) (j : Fin 2) (c : Fin 29) :
    R0Z.SilentReduction.ownProj (F := F) v (.ood j c) = v (.ood j c) := rfl
theorem ownProj_opened (v : Payload K Bat) (q : Fin 262144) (s : Fin 4) (c : Fin 29) :
    R0Z.SilentReduction.ownProj (F := F) v (.opened q s c) = v (.opened q s c) := rfl
theorem ownProj_maskSum (v : Payload K Bat) :
    R0Z.SilentReduction.ownProj (F := F) v .maskSum = 0 := rfl
theorem ownProj_semanticCoeff (v : Payload K Bat) (j : Fin 10) (i : Fin 28) :
    R0Z.SilentReduction.ownProj (F := F) v (.semanticCoeff j i) = 0 := rfl
theorem ownProj_inactiveSum (v : Payload K Bat) :
    R0Z.SilentReduction.ownProj (F := F) v .inactiveSum = 0 := rfl
theorem ownProj_bat (v : Payload K Bat) (b : Bat) :
    R0Z.SilentReduction.ownProj (F := F) v (.bat b) = 0 := rfl

section LRead
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks
  claimsLinear extraLinear dotLinear honestClaims batchLinear oodLinear exactInitialLinear
  coeffsLinear

theorem L_pointClaim_lp (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) (j : Fin 3) (c : Fin 29) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch t (.pointClaim j c) =
      linearPayload (Bat := Bat) π ch t (.pointClaim j c) := rfl
theorem L_extraClaim_lp (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) (c : Fin 29) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch t (.extraClaim c) =
      linearPayload (Bat := Bat) π ch t (.extraClaim c) := rfl
theorem L_ood_lp (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) (j : Fin 2) (c : Fin 29) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch t (.ood j c) =
      linearPayload (Bat := Bat) π ch t (.ood j c) := rfl
theorem L_opened_lp (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (t : Trace K) (q : Fin 262144) (s : Fin 4) (c : Fin 29) :
    R0Z.PayloadSplit.L (Bat := Bat) π B ch t (.opened q s c) =
      linearPayload (Bat := Bat) π ch t (.opened q s c) := rfl


theorem lp_pointClaim (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K)
    (j : Fin 3) (c : Fin 29) :
    linearPayload (Bat := Bat) π ch t (.pointClaim j c) = claimsLinear (alpha ch) j c t := by
  simp only [linearPayload, LinearMap.pi_apply]

theorem lp_extraClaim (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (c : Fin 29) :
    linearPayload (Bat := Bat) π ch t (.extraClaim c) = extraLinear π (alpha ch) c t := by
  simp only [linearPayload, LinearMap.pi_apply]

theorem lp_ood (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K) (j : Fin 2) (c : Fin 29) :
    linearPayload (Bat := Bat) π ch t (.ood j c) =
      oodLinear (ch.circle j) (fun i => t c (π.symm i)) := by
  simp only [linearPayload, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coeffsLinear_apply]

theorem lp_opened (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (t : Trace K)
    (q : Fin 262144) (s : Fin 4) (c : Fin 29) :
    linearPayload (Bat := Bat) π ch t (.opened q s c) =
      if q ∈ ch.queries then
        exactInitialLinear (fun i => t c (π.symm i)) (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)
      else 0 := by
  simp only [linearPayload, LinearMap.pi_apply]
  split_ifs <;> simp only [LinearMap.comp_apply, LinearMap.proj_apply, coeffsLinear_apply,
    LinearMap.zero_apply]

end LRead

/-- The Rust own column of a single-lane balanced word, as a payload. -/
def rustOwn (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : Fin 29) (d r : Fin 1024) (x : K) :
    Payload K Bat := fun cell =>
  let bal := fun (v : Fin 1024 → K) =>
    x * v r - (if r ∈ copyInactiveRows then x * v d else 0)
  match cell with
  | .pointClaim j c => if c = l then bal (rustEq (rustPoints (alpha ch) j)) else 0
  | .extraClaim c => if c = l then bal (fun s => rustHWeight (alpha ch) (π s)) else 0
  | .ood j c => if c = l then
      bal (fun s => rustEvalRow (π s) (ch.circle j).1.1 (ch.circle j).1.2) else 0
  | .opened q s c => if c = l ∧ q ∈ ch.queries then
      bal (fun s' => rustEvalRow (π s')
        (storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex q s))
        (storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex q s))) else 0
  | _ => 0

theorem rustOwn_maskSum (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : Fin 29)
    (d r : Fin 1024) (x : K) : rustOwn (Bat := Bat) π ch l d r x .maskSum = 0 := rfl
theorem rustOwn_semanticCoeff (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : Fin 29)
    (d r : Fin 1024) (x : K) (j : Fin 10) (i : Fin 28) :
    rustOwn (Bat := Bat) π ch l d r x (.semanticCoeff j i) = 0 := rfl
theorem rustOwn_inactiveSum (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : Fin 29)
    (d r : Fin 1024) (x : K) : rustOwn (Bat := Bat) π ch l d r x .inactiveSum = 0 := rfl
theorem rustOwn_bat (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (l : Fin 29)
    (d r : Fin 1024) (x : K) (b : Bat) : rustOwn (Bat := Bat) π ch l d r x (.bat b) = 0 := rfl

/-- **RF-own (K-valued).**  For a mask tape whose pure trace is the balanced
word `balWord d r x` in lane `l` and zero elsewhere, `ownMap` is the Rust own
column `rustOwn`. -/
theorem ownMap_of_lane (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (m : M K F) (l : Fin 29) (d r : Fin 1024) (hr : r ≠ d) (x : K)
    (hw : pureTrace B m l = balWord d r x) (hz : ∀ l', l' ≠ l → pureTrace B m l' = 0) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m = rustOwn π ch l d r x := by
  have hA : (A (Bat := Bat) π B ch).comp inlM m = R0Z.PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) :=
    R0Z.PureRounds.A_pure π B ch m
  have hown : ∀ cell, R0Z.SilentReduction.ownMap (Bat := Bat) π B ch m cell =
      R0Z.SilentReduction.ownProj (F := F) ((A (Bat := Bat) π B ch).comp inlM m) cell := fun _ => rfl
  funext cell
  rw [hown, hA]
  cases cell with
  | maskSum => rw [ownProj_maskSum, rustOwn_maskSum]
  | semanticCoeff j i => rw [ownProj_semanticCoeff, rustOwn_semanticCoeff]
  | inactiveSum => rw [ownProj_inactiveSum, rustOwn_inactiveSum]
  | bat b => rw [ownProj_bat, rustOwn_bat]
  | pointClaim j c =>
    rw [ownProj_pointClaim, L_pointClaim_lp, lp_pointClaim]
    show _ = if c = l then _ else 0
    by_cases hc : c = l
    · rw [if_pos hc]
      subst hc
      exact claim_balWord _ j c _ d r hr x hw
    · rw [if_neg hc, claimsLinear_sum, hz c hc]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  | extraClaim c =>
    rw [ownProj_extraClaim, L_extraClaim_lp, lp_extraClaim]
    show _ = if c = l then _ else 0
    by_cases hc : c = l
    · rw [if_pos hc]
      subst hc
      exact extra_balWord π _ c _ d r hr x hw
    · rw [if_neg hc, extraLinear_sum, hz c hc]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  | ood j c =>
    rw [ownProj_ood, L_ood_lp, lp_ood]
    show _ = if c = l then _ else 0
    by_cases hc : c = l
    · rw [if_pos hc]
      subst hc
      rw [hw, functional_balWord _ π d r hr x, oodLinear_unit, oodLinear_unit]
    · rw [if_neg hc, hz c hc]
      exact map_zero _
  | opened q s c =>
    rw [ownProj_opened, L_opened_lp, lp_opened]
    show _ = if c = l ∧ q ∈ ch.queries then _ else 0
    by_cases hq : q ∈ ch.queries
    · rw [if_pos hq]
      by_cases hc : c = l
      · rw [if_pos ⟨hc, hq⟩]
        subst hc
        rw [hw]
        have hφ := functional_balWord
          ((LinearMap.proj (AspisV5ComponentCConcreteFoldLinearity.childIndex q s)).comp
            (exactInitialLinear (E := K))) π d r hr x
        simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hφ
        rw [hφ, encoder_unit, encoder_unit]
      · rw [if_neg (fun h => hc h.1), hz c hc]
        exact congrFun (map_zero (exactInitialLinear (E := K))) _
    · rw [if_neg hq, if_neg (fun h => hq h.2)]

/-- The checker's mask-only sources (lane `16 + c`, row `r ≥ 1`). -/
theorem ownMap_maskOnlySrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (c : Fin 10) (r : Fin 1024) (hr : r ≠ 0) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (maskOnlySrc (K := K) (F := F) c r) =
      rustOwn π ch ⟨16 + c.val, by omega⟩ 0 r 1 :=
  ownMap_of_lane π B ch _ _ 0 r hr 1 (pureTrace_maskOnlySrc B c r hr)
    (fun l hl => pureTrace_maskOnlySrc_other B c r l hl)

/-- The checker's G sources (lane 27, row `r ≥ 1`, limb `k`). -/
theorem ownMap_gSrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (gSrc (K := K) (F := F) r k) =
      rustOwn π ch 27 0 r (R0P.Mask.towerBasis B k) :=
  ownMap_of_lane π B ch _ _ 0 r hr _ (pureTrace_gSrc B r k hr)
    (fun l hl => pureTrace_gSrc_other B r k l hl)

/-- The checker's D sources (lane 28, row `r ≥ 1`, limb `k`). -/
theorem ownMap_dSrc (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (r : Fin 1024) (k : Fin 4) (hr : r ≠ 0) :
    R0Z.SilentReduction.ownMap (Bat := Bat) π B ch (dSrc (K := K) (F := F) r k) =
      rustOwn π ch 28 0 r (R0P.Mask.towerBasis B k) :=
  ownMap_of_lane π B ch _ _ 0 r hr _ (pureTrace_dSrc B r k hr)
    (fun l hl => pureTrace_dSrc_other B r k l hl)

end Cells

#print axioms sum_mul_balWord
#print axioms functional_eq_sum
#print axioms functional_balWord
#print axioms rustEq_eq
#print axioms openingPoints_eq
#print axioms claim_balWord
#print axioms extra_balWord
#print axioms eval_even_unit
#print axioms eval_odd_unit
#print axioms encoderPair_unit
#print axioms oodLinear_unit
#print axioms encoder_unit
#print axioms lp_pointClaim
#print axioms lp_opened
#print axioms ownMap_of_lane
#print axioms ownMap_maskOnlySrc
#print axioms ownMap_gSrc
#print axioms ownMap_dSrc

end R1Z.RfOwn

end
