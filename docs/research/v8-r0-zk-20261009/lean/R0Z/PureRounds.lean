import R0Z.Shift
import R0Z.Chain
import R0Z.Z4Maps

/-! T2b-2a: the pure-mask round formulas and the easy chain inclusion.
The Z4Maps import supplies the existing silentMasks submodule. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.PureRounds
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView
  R0Z.Partition R0Z.D12 R0Z.Shift R0Z.Chain R0Z.Z4Maps Polynomial
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyInactiveRows copyActiveRowMasks
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

theorem A_pure (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) :
    (A (Bat := Bat) π B ch).comp inlM m = PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) := by
  change PayloadSplit.L (Bat := Bat) π B ch (JointTrace.tapeLinear B (m,0)) = _
  rw [JointTrace.tapeLinear_pure]

theorem roundPoly_L (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) (j : Fin 10) :
    Chain.roundPoly j (PayloadSplit.L (Bat := Bat) π B ch t) =
      PayloadSplit.rounds ch j (fun a => PayloadSplit.maskLinear π B a t) := by
  rw [Chain.roundPoly_apply]
  simp only [PayloadSplit.L_round]
  exact sum_monomial_coeff _ (rounds_natDegree_lt ch j _)

attribute [local irreducible] PayloadSplit.maskLinear

theorem L_maskSum (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) :
    PayloadSplit.L (Bat := Bat) π B ch t .maskSum =
      ∑ bits : Fin 10 → Bool, PayloadSplit.maskLinear π B (ofBool bits) t := by
  simp only [PayloadSplit.L, LinearMap.pi_apply, LinearMap.sum_apply]
  rfl

attribute [local irreducible] A PayloadSplit.L pureTrace

theorem silent_mem_chain0 (h : HonestProver K) (B : PackBasis F)
    (ch : Challenges K) (m : M K F)
    (hs : nonRound (F := F) ((A (Bat := Bat) h.transport B ch).comp inlM m) = 0) :
    (A (Bat := Bat) h.transport B ch).comp inlM m ∈ Chain0 ch := by
  have hsum : (A (Bat := Bat) h.transport B ch).comp inlM m .maskSum = 0 := by
    simpa only [nonRound, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun hs .maskSum
  have hp (c : Fin 29) :
      (A (Bat := Bat) h.transport B ch).comp inlM m (.pointClaim 0 c) = 0 := by
    simpa only [nonRound, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun hs (.pointClaim 0 c)
  have hx : (A (Bat := Bat) h.transport B ch).comp inlM m (.extraClaim 28) = 0 := by
    simpa only [nonRound, LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
      using congrFun hs (.extraClaim 28)
  have hm : claimMask B (alpha ch) ((A (Bat := Bat) h.transport B ch).comp inlM m) = 0 := by
    simp only [claimMask, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, proj_apply, hp, hx, smul_zero, Finset.sum_const_zero, add_zero]
  rw [mem_chain0_iff (F := F)]
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [A_pure, roundPoly_L, rounds_initial ch _ (maskLinear_vdeg _ B _), bsumB_eq_sum]
    simpa only [A_pure, L_maskSum] using hsum
  · intro j
    rw [A_pure, roundPoly_L, roundPoly_L]
    exact rounds_chain ch _ (maskLinear_vdeg _ B _) j
  · have he := Phi0_A (Bat := Bat) h B ch (inlM m)
    change evalRound9 ch ((A (Bat := Bat) h.transport B ch).comp inlM m) -
      claimMask B (alpha ch) ((A (Bat := Bat) h.transport B ch).comp inlM m) = 0 at he
    rw [hm, sub_zero] at he
    exact he

/-- T2b-2a′: maskSum is retained, along with every direct observation. -/
theorem mem_silentMasks_iff (h : HonestProver K) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) :
    m ∈ silentMasks (Bat := Bat) h.transport B ch ↔
      let v := (A (Bat := Bat) h.transport B ch).comp inlM m
      v .maskSum = 0 ∧
      (∀ j c, v (.pointClaim j c) = 0) ∧ (∀ c, v (.extraClaim c) = 0) ∧
      (∀ j c, v (.ood j c) = 0) ∧ v .inactiveSum = 0 ∧
      (∀ b, v (.bat b) = 0) ∧
      (∀ q s c, v (.opened q s c) = 0) := by
  change nonRound (F := F) ((A (Bat := Bat) h.transport B ch).comp inlM m) = 0 ↔ _
  generalize (A (Bat := Bat) h.transport B ch).comp inlM m = v
  simp only [nonRound, LinearMap.pi_apply, LinearMap.proj_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro hz
    exact ⟨hz .maskSum, fun j c => hz (.pointClaim j c),
      fun c => hz (.extraClaim c), fun j c => hz (.ood j c),
      hz .inactiveSum, fun b => hz (.bat b), fun q s c => hz (.opened q s c)⟩
  · rintro ⟨hs, hp, hx, ho, hi, hb, hq⟩
    intro coord
    cases coord with
    | maskSum => exact hs
    | semanticCoeff j i => rfl
    | pointClaim j c => exact hp j c
    | extraClaim c => exact hx c
    | ood j c => exact ho j c
    | inactiveSum => exact hi
    | opened q s c => exact hq q s c
    | bat b => exact hb b

/-- The two source families: w 0 i = 3+22i and w 16 i = 275+150i. -/
def w (family : Nat) (i : Fin 10) : K :=
  ((3 + 22 * i.val + family * (17 + 8 * i.val) : Nat) : K)

/-- Contributions outside the current coordinate. -/
def β (weights : Fin 10 → K) (a : Fin 10 → K) (j : Fin 10) (r : Fin 1024) : K :=
  (∑ i : Fin 10, if i.val < j.val then weights i * a i else 0) +
    ∑ i : Fin 10, if j.val < i.val then weights i * (if rowBits r i then 1 else 0) else 0

/-- Equality weight of the fixed prefix, in the source's MSB-first order. -/
def eqPrefix (a : Fin 10 → K) (r : Fin 1024) (j : Fin 10) : K :=
  ∏ i : Fin 10, if i.val < j.val then bitFactor (rowBits r i) (a i) else 1

theorem w_zero (i : Fin 10) : w (K := K) 0 i = (3 + 22*i.val : Nat) := by
  simp only [w, Nat.zero_mul, Nat.add_zero]

theorem w_sixteen (i : Fin 10) : w (K := K) 16 i = (275 + 150*i.val : Nat) := by
  unfold w
  congr 1
  omega

theorem maskOnly_degree (c : Fin 10) : (R0P.Mask.maskOnlyFactorExponent c).val + 1 ≤ 22 := by
  simp only [R0P.Mask.maskOnlyFactorExponent]
  split_ifs <;> omega

theorem bitFactor_bool (b t : Bool) :
    bitFactor b (if t then (1 : K) else 0) = if b = t then 1 else 0 := by
  cases b <;> cases t <;> simp [bitFactor]

theorem selector_round_match (ch : Challenges K) (j : Fin 10) (z : K)
    (r : Fin 1024) :
    selAt (roundPoint ch j z (fun k => rowBits r ⟨j.val+1+k.val, by omega⟩)) r =
      eqPrefix (alpha ch) r j * bitFactor (rowBits r j) z := by
  rw [selAt_eq_bitWeight]
  have he (i : Fin 10) :
      bitFactor (rowBits r i)
        (roundPoint ch j z (fun k => rowBits r ⟨j.val+1+k.val, by omega⟩) i) =
      (if i.val < j.val then bitFactor (rowBits r i) (alpha ch i) else 1) *
        (if i = j then bitFactor (rowBits r j) z else 1) := by
    by_cases hlo : i.val < j.val
    · have hne : i ≠ j := by intro h; subst i; omega
      simp only [roundPoint, dif_pos hlo, if_pos hlo, if_neg hne, mul_one]
    · by_cases heq : i = j
      · subst i
        simp only [roundPoint, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, one_mul]
      · have hv : i.val ≠ j.val := fun h => heq (Fin.ext h)
        have hi : (⟨j.val+1+(i.val-j.val-1), by omega⟩ : Fin 10) = i := by
          apply Fin.ext; simp only [Fin.val_mk]; omega
        simp only [roundPoint, dif_neg hlo, dif_neg hv, hi, bitFactor_bool,
          if_neg hlo, if_neg heq, ↓reduceIte, mul_one]
  change (∏ i : Fin 10, bitFactor (rowBits r i) _) = _
  simp only [he, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    if_true, eqPrefix]

theorem selector_round_mismatch (ch : Challenges K) (j : Fin 10) (z : K)
    (r : Fin 1024) (tail : Fin (9-j.val) → Bool)
    (hne : tail ≠ fun k => rowBits r ⟨j.val+1+k.val, by omega⟩) :
    selAt (roundPoint ch j z tail) r = 0 := by
  rw [selAt_eq_bitWeight]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  let i : Fin 10 := ⟨j.val+1+k.val, by omega⟩
  have hi : ¬i.val < j.val := by dsimp [i]; omega
  have he : i.val ≠ j.val := by dsimp [i]; omega
  have ht : (⟨i.val-j.val-1, by omega⟩ : Fin (9-j.val)) = k := by
    apply Fin.ext; dsimp [i]; omega
  change (∏ c : Fin 10, bitFactor (rowBits r c) (roundPoint ch j z tail c)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [roundPoint, dif_neg hi, dif_neg he, ht, bitFactor_bool,
    ]
  exact if_neg (Ne.symm hk)

theorem linear_round_match (weights : Fin 10 → K) (ch : Challenges K)
    (j : Fin 10) (z : K) (r : Fin 1024) :
    (∑ i : Fin 10, weights i *
      roundPoint ch j z (fun k => rowBits r ⟨j.val+1+k.val, by omega⟩) i) =
      weights j * z + β weights (alpha ch) j r := by
  have he (i : Fin 10) : weights i *
      roundPoint ch j z (fun k => rowBits r ⟨j.val+1+k.val, by omega⟩) i =
      (if i = j then weights j * z else 0) +
      (if i.val < j.val then weights i * alpha ch i else 0) +
      (if j.val < i.val then weights i * (if rowBits r i then 1 else 0) else 0) := by
    by_cases hlo : i.val < j.val
    · have hne : i ≠ j := by intro h; subst i; omega
      have hng : ¬ j.val < i.val := by omega
      simp only [roundPoint, dif_pos hlo, if_neg hne, if_pos hlo, if_neg hng,
        zero_add, add_zero]
    · by_cases heq : i = j
      · subst i
        simp only [roundPoint, Nat.lt_irrefl, ↓reduceDIte, ↓reduceIte, add_zero]
      · have hv : i.val ≠ j.val := fun h => heq (Fin.ext h)
        have hgt : j.val < i.val := by omega
        have hi : (⟨j.val+1+(i.val-j.val-1), by omega⟩ : Fin 10) = i := by
          apply Fin.ext; simp only [Fin.val_mk]; omega
        simp only [roundPoint, dif_neg hlo, dif_neg hv, hi, if_neg heq,
          if_neg hlo, if_pos hgt, zero_add]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, β, add_assoc]

theorem tail_sum_selector (ch : Challenges K) (j : Fin 10) (z : K)
    (r : Fin 1024) (f : PayloadSplit.PointFunction K) :
    (∑ tail : Fin (9-j.val) → Bool,
      f (roundPoint ch j z tail) * selAt (roundPoint ch j z tail) r) =
      f (roundPoint ch j z (fun k => rowBits r ⟨j.val+1+k.val, by omega⟩)) *
        (eqPrefix (alpha ch) r j * bitFactor (rowBits r j) z) := by
  rw [← selector_round_match]
  apply Fintype.sum_eq_single (fun k : Fin (9-j.val) => rowBits r ⟨j.val+1+k.val, by omega⟩)
  intro tail hne
  rw [selector_round_mismatch ch j z r tail hne, mul_zero]

/-- Equality on the 28 distinct source nodes, with explicit degree bounds. -/
theorem polynomial_ext28 (p q : K[X]) (hp : p.natDegree < 28)
    (hq : q.natDegree < 28) (he : ∀ z : K, p.eval z = q.eval z) : p = q := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p q
    (fun i j hij => nodes_injOn (K := K) (Finset.mem_univ i) (Finset.mem_univ j) hij)
    (fun i : Fin 28 => he (i.val : K))
  simpa only [Fintype.card_fin] using max_lt hp hq

theorem weighted_vdeg (weights : Fin 10 → K) :
    VDeg 10 (fun _ => 1) (fun a => ∑ i, weights i * a i) := by
  apply vdeg_sum Finset.univ
  intro i _
  apply vdeg_smul
  apply vdeg_mono (vdeg_proj i)
  intro k
  simp only [Pi.single_apply]
  split_ifs <;> omega

theorem word_vdeg (u : Fin 1024 → K) :
    VDeg 10 (fun _ => 1) (fun a => ∑ r, selAt a r * u r) :=
  vdeg_honestClaims_zero (fun _ => u) 0

theorem power_word_vdeg (weights : Fin 10 → K) (τ q : K) (e : Nat)
    (u : Fin 1024 → K) :
    VDeg 10 (fun _ => e+1)
      (fun a => τ * (q + (∑ i, weights i * a i)^e) * ∑ r, selAt a r * u r) := by
  have hp := vdeg_pow (weighted_vdeg weights) e
  have hq := vdeg_add (vdeg_const 10 (fun _ => 0) q) hp
  simpa only [Nat.mul_one, Nat.zero_max] using vdeg_mul (vdeg_smul τ hq) (word_vdeg u)

theorem row_power_degree (a b q : K) (e : Nat) (bit : Bool) :
    ((if bit then (X : K[X]) else 1-X) * (C q + (C a * X + C b)^e)).natDegree ≤ e+1 := by
  have hb : (if bit then (X : K[X]) else 1-X).natDegree ≤ 1 := by
    cases bit
    · exact (natDegree_sub_le _ _).trans (by simp)
    · simp
  have ha : (C a * X + C b).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simpa only [natDegree_C, natDegree_X, Nat.zero_add] using
        (natDegree_mul_le (p := C a) (q := (X : K[X])))
    · simp
  have he : (C q + (C a * X + C b)^e).natDegree ≤ e := by
    apply (natDegree_add_le _ _).trans
    apply max_le (by simp)
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le e ha
  exact natDegree_mul_le.trans (by omega)

/-- One symbolic formula covers a power and G's added constant term. -/
theorem power_rounds (weights : Fin 10 → K) (τ q : K) (e : Nat) (he : e ≤ 26)
    (ch : Challenges K) (u : Fin 1024 → K) (j : Fin 10) :
    PayloadSplit.rounds ch j
      (fun a => τ * (q + (∑ i, weights i * a i)^e) * ∑ r, selAt a r * u r) =
      ∑ r, u r • (τ * eqPrefix (alpha ch) r j) •
        ((if rowBits r j then X else 1-X) *
          (C q + (C (weights j)*X + C (β weights (alpha ch) j r))^e)) := by
  apply polynomial_ext28
  · exact rounds_natDegree_lt ch j _
  · apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (fun r _ =>
      (natDegree_smul_le _ _).trans ((natDegree_smul_le _ _).trans
        (row_power_degree _ _ _ _ _))))
    omega
  · intro z
    rw [rounds_eval_of_vdeg ch j _
      (vdeg_mono (power_word_vdeg weights τ q e u) (fun _ => by omega))]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, eval_mul, eval_add,
      eval_C, eval_pow, apply_ite, eval_X, eval_sub, eval_one]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    have hs := tail_sum_selector ch j z r
      (fun a => τ * (q + (∑ i, weights i * a i)^e))
    rw [linear_round_match] at hs
    calc
      _ = (∑ tail : Fin (9-j.val) → Bool,
          (τ * (q + (∑ i, weights i * roundPoint ch j z tail i)^e)) *
            selAt (roundPoint ch j z tail) r) * u r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro tail _
        ring
      _ = _ := by rw [hs]; simp only [bitFactor]; ring

theorem pureRound_maskOnly (B : PackBasis F) (ch : Challenges K)
    (c : Fin 10) (u : Fin 1024 → K) (j : Fin 10) :
    PayloadSplit.rounds ch j (fun a =>
      R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
        R0P.Mask.maskLinear 0 a ^ (R0P.Mask.maskOnlyFactorExponent c).val *
          ∑ r, selAt a r * u r) =
      ∑ r, u r • (R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
        eqPrefix (alpha ch) r j) • ((if rowBits r j then X else 1-X) *
          (C (w 0 j)*X + C (β (w 0) (alpha ch) j r)) ^
            (R0P.Mask.maskOnlyFactorExponent c).val) := by
  simpa only [R0P.Mask.maskLinear, w, zero_add, map_zero] using
    power_rounds (w 0) (R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩)
      0 (R0P.Mask.maskOnlyFactorExponent c).val (by have := maskOnly_degree c; omega) ch u j

theorem pureRound_G (ch : Challenges K) (u : Fin 1024 → K) (j : Fin 10) :
    PayloadSplit.rounds ch j (fun a =>
      (1 + R0P.Mask.maskLinear 16 a ^ 26) * ∑ r, selAt a r * u r) =
      ∑ r, u r • eqPrefix (alpha ch) r j • ((if rowBits r j then X else 1-X) *
        (1 + (C (w 16 j)*X + C (β (w 16) (alpha ch) j r)) ^ 26)) := by
  simpa only [R0P.Mask.maskLinear, w, one_mul, map_one] using
    power_rounds (w 16) 1 1 26 (by omega) ch u j

/-- The mask-only substituted function has coordinate degree at most e_c+1 (at most 22). -/
theorem maskOnly_word_vdeg (B : PackBasis F) (c : Fin 10) (u : Fin 1024 → K) :
    VDeg 10 (fun _ => (R0P.Mask.maskOnlyFactorExponent c).val+1)
      (fun a => R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
        R0P.Mask.maskLinear 0 a ^ (R0P.Mask.maskOnlyFactorExponent c).val *
          ∑ r, selAt a r * u r) := by
  simpa only [w, R0P.Mask.maskLinear, zero_add] using
    power_word_vdeg (w 0)
      (R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩)
      0 (R0P.Mask.maskOnlyFactorExponent c).val u

theorem pureRound_maskOnly_degree (B : PackBasis F) (ch : Challenges K)
    (c : Fin 10) (u : Fin 1024 → K) (j : Fin 10) :
    (PayloadSplit.rounds ch j (fun a =>
      R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
        R0P.Mask.maskLinear 0 a ^ (R0P.Mask.maskOnlyFactorExponent c).val *
          ∑ r, selAt a r * u r)).natDegree ≤ (R0P.Mask.maskOnlyFactorExponent c).val+1 := by
  rw [pureRound_maskOnly]
  apply natDegree_sum_le_of_forall_le
  intro r _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_smul_le _ _).trans
  simpa only [map_zero, zero_add] using
    row_power_degree (w 0 j) (β (w 0) (alpha ch) j r) (0 : K)
      (R0P.Mask.maskOnlyFactorExponent c).val (rowBits r j)

/-- A symbolic Boolean cube has 2^n elements. -/
theorem sum_bool_const (n : Nat) (c : K) :
    (∑ _ : Fin n → Bool, c) = (2 : K)^n * c := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Isolate one Boolean coordinate by a tuple equivalence, without enumerating a cube. -/
theorem sum_bool_coordinate (n : Nat) (k : Fin n) (f : Bool → K) :
    (∑ b : Fin n → Bool, f (b k)) = (2 : K)^(n-1) * (f false + f true) := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
    have hs : (∑ b : Fin (n+1) → Bool, f (b k)) =
        ∑ p : Bool × (Fin n → Bool), f p.1 := by
      exact (Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Bool) k)
        (fun p => f p.1) (fun b => f (b k))
        (fun p => by simp only [Fin.insertNthEquiv_apply, Fin.insertNth_apply_same])).symm
    rw [hs, Fintype.sum_prod_type]
    simp only [sum_bool_const, Fintype.sum_bool, Nat.add_sub_cancel]
    ring

theorem sum_bool_power (n : Nat) (k : Fin n) (e : Nat) :
    (∑ b : Fin n → Bool, (if b k then (1 : K) else 0)^e) =
      (2 : K)^(n-1) * (if e = 0 then 2 else 1) := by
  rw [sum_bool_coordinate n k (fun b => (if b then (1 : K) else 0)^e)]
  by_cases he : e = 0
  · simp only [he, pow_zero, if_true]; ring
  · simp only [Bool.false_eq_true, if_false, if_true, zero_pow he, one_pow,
      zero_add, if_neg he]

theorem coordinate_power_vdeg (k : Fin 10) (e : Nat) :
    VDeg 10 (fun _ => e) (fun a : Fin 10 → K => a k ^ e) := by
  apply vdeg_mono (vdeg_pow (vdeg_proj k) e)
  intro i
  simp only [Pi.single_apply]
  split_ifs <;> simp

/-- The round of one coordinate monomial, before specializing to Libra's two coordinates. -/
theorem coordinate_power_round (ch : Challenges K) (k j : Fin 10) (e : Nat)
    (he : e ≤ 27) :
    PayloadSplit.rounds ch j (fun a => a k ^ e) =
      if j.val < k.val then C ((2 : K)^(8-j.val) * (if e = 0 then 2 else 1))
      else if j = k then C ((2 : K)^(9-j.val)) * X^e
      else C ((2 : K)^(9-j.val) * alpha ch k ^ e) := by
  apply polynomial_ext28
  · exact rounds_natDegree_lt ch j _
  · by_cases hjk : j.val < k.val
    · rw [if_pos hjk, natDegree_C]; omega
    · rw [if_neg hjk]
      by_cases heq : j = k
      · rw [if_pos heq]
        exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le _ e) (by omega)
      · rw [if_neg heq, natDegree_C]; omega
  · intro z
    rw [rounds_eval_of_vdeg ch j _
      (vdeg_mono (coordinate_power_vdeg k e) (fun _ => he))]
    by_cases hjk : j.val < k.val
    · have hkj : ¬ k.val < j.val := by omega
      have hne : k.val ≠ j.val := by omega
      simp only [if_pos hjk, eval_C, roundPoint, dif_neg hkj, dif_neg hne]
      have hs := sum_bool_power (K := K) (9-j.val) ⟨k.val-j.val-1, by omega⟩ e
      simpa only [show 9-j.val-1 = 8-j.val by omega] using hs
    · by_cases heq : j = k
      · subst k
        simp only [if_neg hjk, if_true, if_false, roundPoint, Nat.lt_irrefl, ↓reduceDIte,
          eval_mul, eval_C, eval_pow, eval_X, sum_bool_const]
      · have hkj : k.val < j.val := by
          have hne : j.val ≠ k.val := fun h => heq (Fin.ext h)
          omega
        simp only [if_neg hjk, if_neg heq, roundPoint, dif_pos hkj, eval_C,
          sum_bool_const]

/-- T2b-2a″: cell d has local degree d % 28, not degree d. -/
theorem pureRound_libra (ch : Challenges K) (d : Fin 56) (j : Fin 10) :
    let k : Fin 10 := if d.val < 28 then 8 else 9
    let e := d.val % 28
    PayloadSplit.rounds ch j (fun a => a k ^ e) =
      if j.val < k.val then C ((2 : K)^(8-j.val) * (if e = 0 then 2 else 1))
      else if j = k then C ((2 : K)^(9-j.val)) * X^e
      else C ((2 : K)^(9-j.val) * alpha ch k ^ e) := by
  dsimp only
  exact coordinate_power_round ch _ j _ (Nat.le_of_lt_succ (Nat.mod_lt _ (by omega)))

theorem pureLibra_maskSum (d : Fin 56) :
    let k : Fin 10 := if d.val < 28 then 8 else 9
    let e := d.val % 28
    (∑ b : Fin 10 → Bool, (ofBool b : Fin 10 → K) k ^ e) =
      (512 : K) * (if e = 0 then 2 else 1) := by
  dsimp only
  rw [show (512 : K) = (2 : K)^(10-1) by norm_num]
  exact sum_bool_power 10 _ _

/-- The pure trace is the actual affine mask applied to the zero trace. -/
theorem pureTrace_applyAff (B : PackBasis F) (m : M K F) :
    pureTrace B m = applyAff B 0 (pureAff m) := by
  rw [applyAff_eq_base_add]
  have hz : traceBase (0 : Trace K) = 0 := by
    funext c r
    simp only [traceBase, Pi.zero_apply, ite_self]
  rw [hz, zero_add]
  simp only [pureTrace, LinearMap.comp_apply]

theorem pureTrace_maskOnly_word (B : PackBasis F) (m : M K F) (c : Fin 10) :
    pureTrace B m ⟨16+c.val, by omega⟩ =
      maskOnlyColumns (Sum.elim 0 (pureAff m)) c := by
  rw [pureTrace_applyAff]
  funext r
  simp only [applyAff, Fin.val_mk, if_neg (show ¬16+c.val < 16 by omega),
    dif_pos (show 16+c.val < 26 by omega)]
  congr 2
  omega

theorem pureTrace_G_word (B : PackBasis F) (m : M K F) :
    pureTrace B m 27 = balance 0 (extensionRaw B (Sum.elim 0 (pureAff m)) 0) := by
  rw [pureTrace_applyAff]
  rfl

theorem pureTrace_D_word (B : PackBasis F) (m : M K F) :
    pureTrace B m 28 = dWord B (Sum.elim 0 (pureAff m)) := by
  rw [pureTrace_applyAff]
  rfl

/-- Only the stated column is read by each point-claim functional. -/
theorem claims_zero_of_word_zero (t : Trace K) (a : Fin 10 → K)
    (j : Fin 3) (l : Fin 29) (hz : t l = 0) : honestClaims t a j l = 0 := by
  simp only [honestClaims, hz, AspisR0.LinearDual.dot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero]

theorem extra_zero_of_word_zero (π : Fin 1024 ≃ Fin 1024) (t : Trace K)
    (a : Fin 10 → K) (l : Fin 29) (hz : t l = 0) :
    extraLinear π a l t = 0 := by
  simp only [extraLinear, LinearMap.comp_apply, LinearMap.proj_apply, hz,
    map_zero]

/-- The mask-only factor on a trace supported in that lane. -/
theorem maskLinear_maskOnly (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (a : Fin 10 → K) (t : Trace K) (c : Fin 10)
    (hs : ∀ l : Fin 29, l ≠ ⟨16+c.val, by omega⟩ → t l = 0) :
    PayloadSplit.maskLinear π B a t =
      R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
        R0P.Mask.maskLinear 0 a ^ (R0P.Mask.maskOnlyFactorExponent c).val *
          ∑ r, selAt a r * t ⟨16+c.val, by omega⟩ r := by
  have hc1 (i : Fin 16) : honestClaims t a 0 (Fin.castLE (by omega) i) = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_castLE, Fin.val_mk] at this
    omega
  have hg : honestClaims t a 0 27 = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    have := congrArg Fin.val he
    change 27 = 16+c.val at this
    omega
  have hd : extraLinear π a 28 t = 0 := by
    apply extra_zero_of_word_zero
    apply hs
    intro he
    have := congrArg Fin.val he
    change 28 = 16+c.val at this
    omega
  have hm (i : Fin 10) (hne : i ≠ c) :
      honestClaims t a 0 ⟨16+i.val, by omega⟩ = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    apply hne
    apply Fin.ext
    have := congrArg Fin.val he
    simp only [Fin.val_mk] at this
    omega
  simp only [PayloadSplit.maskLinear, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, claimsLinear_apply, hc1, hg, hd,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  rw [Fintype.sum_eq_single c (fun i hi => by rw [hm i hi, mul_zero])]
  have ht : (⟨c.val%4, Nat.mod_lt _ (by omega)⟩ : Fin 4) =
      ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ := by
    apply Fin.ext
    change c.val%4 = (16+c.val)%4
    omega
  simp only [R0P.Mask.maskFactors, R0P.Mask.mulTowerBasis, ht]
  rfl

theorem maskLinear_G (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (a : Fin 10 → K) (t : Trace K) (hs : ∀ l : Fin 29, l ≠ 27 → t l = 0) :
    PayloadSplit.maskLinear π B a t =
      (1 + R0P.Mask.maskLinear 16 a ^ 26) * ∑ r, selAt a r * t 27 r := by
  have hc1 (i : Fin 16) : honestClaims t a 0 (Fin.castLE (by omega) i) = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    have := congrArg Fin.val he
    change i.val = 27 at this
    omega
  have hm (i : Fin 10) : honestClaims t a 0 ⟨16+i.val, by omega⟩ = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    have := congrArg Fin.val he
    change 16+i.val = 27 at this
    omega
  have hd : extraLinear π a 28 t = 0 :=
    extra_zero_of_word_zero π t a 28 (hs 28 (by decide))
  simp only [PayloadSplit.maskLinear, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, claimsLinear_apply, hc1, hm, hd,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, R0P.Mask.maskFactors]
  rfl

theorem maskLinear_D (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (a : Fin 10 → K) (t : Trace K) (hs : ∀ l : Fin 29, l ≠ 28 → t l = 0) :
    PayloadSplit.maskLinear π B a t = extraLinear π a 28 t := by
  have hz (l : Fin 29) (hl : l.val < 28) : honestClaims t a 0 l = 0 := by
    apply claims_zero_of_word_zero
    apply hs
    intro he
    subst l
    exact (Nat.lt_irrefl 28) hl
  have hc (i : Fin 16) : honestClaims t a 0 (Fin.castLE (by omega) i) = 0 :=
    hz _ (by simp only [Fin.val_castLE]; omega)
  have hm (i : Fin 10) : honestClaims t a 0 ⟨16+i.val, by omega⟩ = 0 :=
    hz _ (by simp only [Fin.val_mk]; omega)
  simp only [PayloadSplit.maskLinear, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, claimsLinear_apply, hc, hm, hz 27 (by omega),
    mul_zero, Finset.sum_const_zero, zero_add]

theorem extra_coefficient_unit (π : Fin 1024 ≃ Fin 1024) (t : Trace K)
    (a : Fin 10 → K) (d : Fin 56)
    (hu : coeffsOf π t 28 = Pi.single ⟨d.val, by omega⟩ 1) :
    extraLinear π a 28 t = a (if d.val < 28 then 8 else 9) ^ (d.val%28) := by
  rw [extraLinear_apply]
  unfold R0P.Mask.honestExtra
  rw [hu]
  simp only [AspisR0.RoundNormalization.dot, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change libraWeight a ⟨d.val, by omega⟩ = _
  by_cases hd : d.val < 28
  · simp only [libraWeight, Fin.val_mk, if_pos hd, Nat.mod_eq_of_lt hd]
  · have hm : d.val%28 = d.val-28 := by omega
    simp only [libraWeight, Fin.val_mk, if_neg hd, if_pos d.isLt, hm]

/-- A zero raw lane stays zero under its symbolic balance. -/
theorem pureTrace_maskOnly_zero (B : PackBasis F) (m : M K F) (c : Fin 10)
    (hz : ∀ r, m.1 (c,r) = 0) : pureTrace B m ⟨16+c.val, by omega⟩ = 0 := by
  rw [pureTrace_maskOnly_word]
  have hr : maskOnlyRaw (Sum.elim 0 (pureAff m)) c = 0 := by
    funext r
    change (m.1 (c,r) : K) = 0
    rw [hz]
    rfl
  funext r
  simp only [maskOnlyColumns, hr, balance, Pi.zero_apply, Finset.sum_const_zero,
    neg_zero, ite_self]

theorem pureTrace_G_zero (B : PackBasis F) (m : M K F)
    (hz : m.2.1 = 0) : pureTrace B m 27 = 0 := by
  rw [pureTrace_G_word]
  have hr : extensionRaw B (Sum.elim 0 (pureAff m)) 0 = 0 := by
    funext r
    change pack4 B (fun limb => (m.2.1 (r,limb) : K)) = 0
    simp only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, pack4, mul_zero, add_zero]
  funext r
  simp only [hr, balance, Pi.zero_apply, Finset.sum_const_zero, neg_zero, ite_self]

theorem pureTrace_D_zero (B : PackBasis F) (m : M K F)
    (hz : m.2.2 = 0) : pureTrace B m 28 = 0 := by
  rw [pureTrace_D_word]
  have hr : extensionRaw B (Sum.elim 0 (pureAff m)) 2 = 0 := by
    funext r
    change pack4 B (fun limb => (m.2.2 (r,limb) : K)) = 0
    simp only [hz, Pi.zero_apply, ZeroMemClass.coe_zero, pack4, mul_zero, add_zero]
  funext r
  simp only [dWord, hr, balance, Pi.zero_apply, Finset.sum_const_zero, neg_zero, ite_self]

/-- Raw support in mask-only lane c supplies the support premise of L_pure_maskOnly. -/
theorem pureTrace_maskOnly_support (B : PackBasis F) (m : M K F) (c : Fin 10)
    (hm : ∀ i : Fin 10, i ≠ c → ∀ r, m.1 (i,r) = 0)
    (hg : m.2.1 = 0) (hd : m.2.2 = 0) :
    ∀ l : Fin 29, l ≠ ⟨16+c.val, by omega⟩ → pureTrace B m l = 0 := by
  intro l hne
  by_cases hf : l.val < 16 ∨ l.val = 26
  · exact pureTrace_fixed B m l hf
  · by_cases hl : l.val < 26
    · let i : Fin 10 := ⟨l.val-16, by omega⟩
      have he : l = (⟨16+i.val, by omega⟩ : Fin 29) := by
        apply Fin.ext; dsimp [i]; omega
      have hi : i ≠ c := by intro h; apply hne; simpa only [h] using he
      rw [he]
      exact pureTrace_maskOnly_zero B m i (hm i hi)
    · by_cases he : l = 27
      · subst l; exact pureTrace_G_zero B m hg
      · have he' : l = 28 := by
          apply Fin.ext
          have hn : l.val ≠ 27 := fun h => he (Fin.ext h)
          change l.val = 28
          omega
        subst l
        exact pureTrace_D_zero B m hd

/-- Raw support in G supplies the support premise of L_pure_G. -/
theorem pureTrace_G_support (B : PackBasis F) (m : M K F)
    (hm : m.1 = 0) (hd : m.2.2 = 0) :
    ∀ l : Fin 29, l ≠ 27 → pureTrace B m l = 0 := by
  intro l hne
  by_cases hf : l.val < 16 ∨ l.val = 26
  · exact pureTrace_fixed B m l hf
  · by_cases hl : l.val < 26
    · let i : Fin 10 := ⟨l.val-16, by omega⟩
      have he : l = (⟨16+i.val, by omega⟩ : Fin 29) := by
        apply Fin.ext; dsimp [i]; omega
      rw [he]
      exact pureTrace_maskOnly_zero B m i (fun r => by rw [hm]; rfl)
    · have he : l = 28 := by
        apply Fin.ext
        have hn : l.val ≠ 27 := fun h => hne (Fin.ext h)
        change l.val = 28
        omega
      subst l
      exact pureTrace_D_zero B m hd

/-- Raw support in D supplies the support premise of L_pure_libra. -/
theorem pureTrace_D_support (B : PackBasis F) (m : M K F)
    (hm : m.1 = 0) (hg : m.2.1 = 0) :
    ∀ l : Fin 29, l ≠ 28 → pureTrace B m l = 0 := by
  intro l hne
  by_cases hf : l.val < 16 ∨ l.val = 26
  · exact pureTrace_fixed B m l hf
  · by_cases hl : l.val < 26
    · let i : Fin 10 := ⟨l.val-16, by omega⟩
      have he : l = (⟨16+i.val, by omega⟩ : Fin 29) := by
        apply Fin.ext; dsimp [i]; omega
      rw [he]
      exact pureTrace_maskOnly_zero B m i (fun r => by rw [hm]; rfl)
    · have he : l = 27 := by
        apply Fin.ext
        have hn : l.val ≠ 28 := fun h => hne (Fin.ext h)
        change l.val = 27
        omega
      subst l
      exact pureTrace_G_zero B m hg

/-- The post-balance mask-only word is the input of the row formula. -/
theorem L_pure_maskOnly (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (c : Fin 10) (j : Fin 10)
    (hm : ∀ i : Fin 10, i ≠ c → ∀ r, m.1 (i,r) = 0)
    (hg : m.2.1 = 0) (hd : m.2.2 = 0) :
    Chain.roundPoly j (PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m)) =
      ∑ r, maskOnlyColumns (Sum.elim 0 (pureAff m)) c r •
        (R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
          eqPrefix (alpha ch) r j) • ((if rowBits r j then X else 1-X) *
            (C (w 0 j)*X + C (β (w 0) (alpha ch) j r)) ^
              (R0P.Mask.maskOnlyFactorExponent c).val) := by
  rw [roundPoly_L]
  have hs := pureTrace_maskOnly_support B m c hm hg hd
  have hf := funext (fun a => maskLinear_maskOnly π B a (pureTrace B m) c hs)
  rw [hf, pureTrace_maskOnly_word, pureRound_maskOnly]

/-- G uses its balanced packed word, with the degree-26 factor plus one. -/
theorem L_pure_G (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (j : Fin 10)
    (hm : m.1 = 0) (hd : m.2.2 = 0) :
    Chain.roundPoly j (PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m)) =
      ∑ r, balance 0 (extensionRaw B (Sum.elim 0 (pureAff m)) 0) r •
        eqPrefix (alpha ch) r j • ((if rowBits r j then X else 1-X) *
          (1 + (C (w 16 j)*X + C (β (w 16) (alpha ch) j r)) ^ 26)) := by
  rw [roundPoly_L]
  have hs := pureTrace_G_support B m hm hd
  have hf := funext (fun a => maskLinear_G π B a (pureTrace B m) hs)
  rw [hf, pureTrace_G_word, pureRound_G]

/-- Coefficient d is selected only after balancing the D row word and transporting it. -/
theorem L_pure_libra (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (d : Fin 56) (j : Fin 10)
    (hm : m.1 = 0) (hg : m.2.1 = 0)
    (hu : (fun k => dWord B (Sum.elim 0 (pureAff m)) (π.symm k)) =
      Pi.single (⟨d.val, by omega⟩ : Fin 1024) 1) :
    let k : Fin 10 := if d.val < 28 then 8 else 9
    let e := d.val%28
    Chain.roundPoly j (PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m)) =
      if j.val < k.val then C ((2 : K)^(8-j.val) * (if e = 0 then 2 else 1))
      else if j = k then C ((2 : K)^(9-j.val)) * X^e
      else C ((2 : K)^(9-j.val) * alpha ch k ^ e) := by
  have hs := pureTrace_D_support B m hm hg
  have hu' : coeffsOf π (pureTrace B m) 28 = Pi.single ⟨d.val, by omega⟩ 1 := by
    change (fun k => pureTrace B m 28 (π.symm k)) = _
    rw [pureTrace_D_word]
    exact hu
  have hf : (fun a => PayloadSplit.maskLinear π B a (pureTrace B m)) =
      fun a => a (if d.val < 28 then 8 else 9) ^ (d.val%28) := by
    funext a
    rw [maskLinear_D π B a _ hs, extra_coefficient_unit π _ a d hu']
  dsimp only
  rw [roundPoly_L, hf]
  exact pureRound_libra ch d j

theorem L_pure_libra_maskSum (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (d : Fin 56)
    (hm : m.1 = 0) (hg : m.2.1 = 0)
    (hu : (fun k => dWord B (Sum.elim 0 (pureAff m)) (π.symm k)) =
      Pi.single (⟨d.val, by omega⟩ : Fin 1024) 1) :
    PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) .maskSum =
      (512 : K) * (if d.val%28 = 0 then 2 else 1) := by
  have hs := pureTrace_D_support B m hm hg
  have hu' : coeffsOf π (pureTrace B m) 28 = Pi.single ⟨d.val, by omega⟩ 1 := by
    change (fun k => pureTrace B m 28 (π.symm k)) = _
    rw [pureTrace_D_word]
    exact hu
  rw [L_maskSum]
  simp_rw [maskLinear_D π B _ _ hs, extra_coefficient_unit π _ _ d hu']
  exact pureLibra_maskSum d

/-- Reconstructing the round polynomial preserves each disclosed coefficient. -/
theorem roundPoly_coeff_L (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (t : Trace K) (j : Fin 10) (i : Fin 28) :
    (Chain.roundPoly j (PayloadSplit.L (Bat := Bat) π B ch t)).coeff i.val =
      PayloadSplit.L (Bat := Bat) π B ch t (.semanticCoeff j i) := by
  rw [roundPoly_L, PayloadSplit.L_round]


theorem L_pure_maskOnly_coeff (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (c : Fin 10) (j : Fin 10) (i : Fin 28)
    (hm : ∀ i : Fin 10, i ≠ c → ∀ r, m.1 (i,r) = 0)
    (hg : m.2.1 = 0) (hd : m.2.2 = 0) :
    PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) (.semanticCoeff j i) =
      (∑ r, maskOnlyColumns (Sum.elim 0 (pureAff m)) c r •
        (R0P.Mask.towerBasis B ⟨(16+c.val)%4, Nat.mod_lt _ (by omega)⟩ *
          eqPrefix (alpha ch) r j) • ((if rowBits r j then X else 1-X) *
            (C (w 0 j)*X + C (β (w 0) (alpha ch) j r)) ^
              (R0P.Mask.maskOnlyFactorExponent c).val)).coeff i.val := by
  rw [← roundPoly_coeff_L]
  exact congrArg (fun p : K[X] => p.coeff i.val) (L_pure_maskOnly π B ch m c j hm hg hd)

theorem L_pure_G_coeff (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (j : Fin 10) (i : Fin 28)
    (hm : m.1 = 0) (hd : m.2.2 = 0) :
    PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) (.semanticCoeff j i) =
      (∑ r, balance 0 (extensionRaw B (Sum.elim 0 (pureAff m)) 0) r •
        eqPrefix (alpha ch) r j • ((if rowBits r j then X else 1-X) *
          (1 + (C (w 16 j)*X + C (β (w 16) (alpha ch) j r)) ^ 26))).coeff i.val := by
  rw [← roundPoly_coeff_L]
  exact congrArg (fun p : K[X] => p.coeff i.val) (L_pure_G π B ch m j hm hd)

theorem L_pure_libra_coeff (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (ch : Challenges K) (m : M K F) (d : Fin 56) (j : Fin 10) (i : Fin 28)
    (hm : m.1 = 0) (hg : m.2.1 = 0)
    (hu : (fun k => dWord B (Sum.elim 0 (pureAff m)) (π.symm k)) =
      Pi.single (⟨d.val, by omega⟩ : Fin 1024) 1) :
    let k : Fin 10 := if d.val < 28 then 8 else 9
    let e := d.val%28
    PayloadSplit.L (Bat := Bat) π B ch (pureTrace B m) (.semanticCoeff j i) =
      (if j.val < k.val then C ((2 : K)^(8-j.val) * (if e = 0 then 2 else 1))
      else if j = k then C ((2 : K)^(9-j.val)) * X^e
      else C ((2 : K)^(9-j.val) * alpha ch k ^ e)).coeff i.val := by
  dsimp only
  rw [← roundPoly_coeff_L]
  exact congrArg (fun p : K[X] => p.coeff i.val) (L_pure_libra π B ch m d j hm hg hu)

#print axioms mem_silentMasks_iff
#print axioms L_pure_maskOnly_coeff
#print axioms L_pure_G_coeff
#print axioms L_pure_libra_coeff
#print axioms L_pure_libra_maskSum
#print axioms pureRound_libra
#print axioms silent_mem_chain0
#print axioms pureRound_maskOnly
#print axioms pureRound_G
end R0Z.PureRounds
