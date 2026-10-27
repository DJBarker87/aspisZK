import R1FoldCoefficientBridge
import R1.RepeatedLift

/-! J4-R1(a): payload-free algebra of the R1 batched opening block
(DESIGN-R1-PRIVACY-MODEL §4, LOG D30).

Five identities, each over an arbitrary message/weight vector and every
challenge value:
* `s2b_identity`  round-1 boundary = quarter · round-0 polynomial at α₀;
* `s1_identity`   round-1 polynomial at α₁ = Σ_e final_e · w2_e;
* `s2a_identity`  round-0 boundary = quarter · Σ_k κ^k ℓ_k(q);
* `circ_identity` folded symbol u = coefficient fold of the four circle channels;
* `line_identity` the line-domain fold of the four stored children of v equals
  the 64-coefficient encoding of the α₁-folded message at v
  (`line_layer_identity`: the whole 2^18 → 2^16 layer).

No payload, transcript, or challenge distribution appears.  The line inverse
table `lineInverse` is stated through the stored line-18 nodes; its equality
with the Rust `QueryGeometry` table is a refinement item, not proved here. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.BatchedAlgebra

open scoped BigOperators

/-! ## The two `childIndex` definitions -/

/-- `AspisR1.childIndex` (spend-path NaturalProjection) and the AspisFormal
`childIndex` are the same flat index `4 i + s`. -/
theorem childIndex_bridge {n : Nat} (i : Fin n) (s : Fin 4) :
    AspisR1.childIndex i s = AspisV5ComponentCConcreteFoldLinearity.childIndex i s :=
  rfl

section Generic

variable {K : Type} [Field K]

/-! ## Round relations (S2b, S1, S2a) -/

/-- S2b: the boundary of the second round polynomial is a quarter of the
first round polynomial evaluated at α₀.  `q` is any 1024-coefficient batched
vector, `w` any weight vector. -/
theorem s2b_identity (alpha0 : K) (q w : Fin (4 * 256) → K) :
    (AspisR1.RoundPairing.roundPolynomial (n := 64)
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 alpha0 q)
        (AspisR1.RoundPairing.dualFold (n := 256) alpha0 w)).coeff 0 +
      (AspisR1.RoundPairing.roundPolynomial (n := 64)
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 alpha0 q)
        (AspisR1.RoundPairing.dualFold (n := 256) alpha0 w)).coeff 4 =
      AspisR1.RoundPairing.quarter *
        (AspisR1.RoundPairing.roundPolynomial (n := 256) q w).eval alpha0 := by
  rw [AspisR1.RoundPairing.round_boundary, AspisR1.RoundPairing.round_eval,
    AspisR1.FoldCoefficientBridge.coefficientFoldLayer_eq_primalFold]
  try rfl

/-- S1: the second round polynomial at α₁ is the pairing of the final
coefficients with the twice-folded weights. -/
theorem s1_identity (alpha1 : K) (q1 w1 : Fin (4 * 64) → K) :
    (AspisR1.RoundPairing.roundPolynomial (n := 64) q1 w1).eval alpha1 =
      ∑ e : Fin 64,
        AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha1 q1 e *
          AspisR1.RoundPairing.dualFold (n := 64) alpha1 w1 e := by
  rw [AspisR1.RoundPairing.round_eval,
    AspisR1.FoldCoefficientBridge.coefficientFoldLayer_eq_primalFold]
  try rfl

/-- The κ-batched weight vector of seven linear functionals:
`w j = Σ_k κ^k ℓ_k(e_j)`. -/
def weightsOf {N : Nat} (kappa : K) (ell : Fin 7 → ((Fin N → K) →ₗ[K] K)) :
    Fin N → K :=
  fun j => ∑ k : Fin 7, kappa ^ k.val * ell k (Pi.single j 1)

/-- Pairing with the batched weights is the κ-batch of the functionals. -/
theorem dot_weightsOf {N : Nat} (kappa : K)
    (ell : Fin 7 → ((Fin N → K) →ₗ[K] K)) (q : Fin N → K) :
    AspisR1.RoundPairing.dot q (weightsOf kappa ell) =
      ∑ k : Fin 7, kappa ^ k.val * ell k q := by
  have hq : q = ∑ j : Fin N, q j • (Pi.single j (1 : K) : Fin N → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have key (k : Fin 7) : ell k q = ∑ j : Fin N, q j * ell k (Pi.single j 1) := by
    conv_lhs => rw [hq]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [AspisR1.RoundPairing.dot, weightsOf, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- S2a: the boundary of the first round polynomial is a quarter of the
κ-batched claim `Σ_k κ^k ℓ_k(q)`. -/
theorem s2a_identity (kappa : K)
    (ell : Fin 7 → ((Fin (4 * 256) → K) →ₗ[K] K)) (q : Fin (4 * 256) → K) :
    (AspisR1.RoundPairing.roundPolynomial (n := 256) q (weightsOf kappa ell)).coeff 0 +
      (AspisR1.RoundPairing.roundPolynomial (n := 256) q (weightsOf kappa ell)).coeff 4 =
      AspisR1.RoundPairing.quarter * ∑ k : Fin 7, kappa ^ k.val * ell k q := by
  rw [AspisR1.RoundPairing.round_boundary, dot_weightsOf]

/-! ## Line-fold algebra on one quartet -/

/-- Field identity behind the line fold: for four nodes `x, -x, w, -w` whose
first doublings are `z, z, -z, -z`, the nested butterfly with inverse table
`(2x)⁻¹, -(2(-w))⁻¹, (2z)⁻¹` applied to the four natural-basis values
`c₀ + x c₁ + T₂(x) c₂ + x T₂(x) c₃` returns `Σ_t α^t c_t`. -/
theorem lineFold_quartet (h2 : (2 : K) ≠ 0) (alpha : K) (x c : Fin 4 → K)
    (h1 : x 1 = -x 0) (h3 : x 3 = -x 2)
    (hT : AspisCircleTensorBinding.doubledFactor (x 2) 1 =
      -AspisCircleTensorBinding.doubledFactor (x 0) 1)
    (hx0 : x 0 ≠ 0) (hx2 : x 2 ≠ 0)
    (hz : AspisCircleTensorBinding.doubledFactor (x 0) 1 ≠ 0)
    (i0 i1 i2 : K) (hi0 : i0 = (2 * x 0)⁻¹) (hi1 : i1 = -(2 * x 3)⁻¹)
    (hi2 : i2 = (2 * AspisCircleTensorBinding.doubledFactor (x 0) 1)⁻¹) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha i0 i1 i2
        (fun s => c 0 + x s * c 1 +
          AspisCircleTensorBinding.doubledFactor (x s) 1 * c 2 +
          x s * AspisCircleTensorBinding.doubledFactor (x s) 1 * c 3) =
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha c := by
  have hneg (z : K) : AspisCircleTensorBinding.doubledFactor (-z) 1 =
      AspisCircleTensorBinding.doubledFactor z 1 := by
    simp only [AspisCircleTensorBinding.doubledFactor, neg_sq]
  have hi1' : i1 = (2 * x 2)⁻¹ := by
    rw [hi1, h3, mul_neg, inv_neg, neg_neg]
  subst hi0 hi2
  rw [hi1']
  simp only [AspisV5ComponentCConcreteFoldLinearity.lineFoldValue,
    AspisV5ComponentCConcreteFoldLinearity.pairFoldValue,
    AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue]
  rw [h1, h3, hneg (x 0), hneg (x 2), hT]
  field_simp
  ring

end Generic

/-! ## Circle fold (C_u) and line fold (L_u) on the exact encoders -/

section Encoders

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- C_u: the exact log-18 encoding of the α₀-folded message at `u` is the
coefficient fold of the four circle channels of the initial encoding at `u`. -/
theorem circ_identity (alpha0 : K) (q : Fin 1024 → K) (u : Fin 262144) :
    AspisWide.FinalEncoder.exactFinalLinear
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 alpha0 q) u =
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha0
        (fun s => AspisR1.FirstFold.channels
          (AspisWide.InitialEncoder.exactInitialEncoder q) s u) :=
  (congrFun (AspisR1.FirstFold.fold_encoded alpha0 q) u).symm

/-- Own-silent form of C_u: a zero opened fibre gives a zero folded value. -/
theorem circ_zero_of_fibre_zero (alpha0 : K) (q : Fin 1024 → K) (u : Fin 262144)
    (hz : AspisR1.FirstFold.fibre (AspisWide.InitialEncoder.exactInitialEncoder q) u = 0) :
    AspisWide.FinalEncoder.exactFinalLinear
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 256 alpha0 q) u = 0 := by
  rw [circ_identity]
  have h0 (s : Fin 4) :
      AspisR1.FirstFold.channels (AspisWide.InitialEncoder.exactInitialEncoder q) s u = 0 := by
    simp only [AspisR1.FirstFold.channels, hz]
    fin_cases s <;>
      simp [AspisR1.FirstFold.fibreTransform,
        AspisV5FriConcreteEncoderCommutation.radix4Decode]
  simp [AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue, h0]

/-- Public M31 inverse table of the line fold at parent `v`:
`(2x)⁻¹, -(2y)⁻¹, (2z)⁻¹` with `x` the stored node of child 0, `y` that of
child 3 and `z = 2x² - 1` (Rust `line_fold`: x = node(4v), y = node(4v+3)). -/
def lineInverse (v : Fin 65536) : Fin 3 → ZMod AspisCircleGroupOrder.P :=
  ![(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0))⁻¹,
    -(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3))⁻¹,
    (2 * (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18
        (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1))⁻¹]

/-- The embedded stored line-18 node of child `s` of parent `v`. -/
def lineNode (v : Fin 65536) (s : Fin 4) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (AspisV7ExactOneFoldDomains.storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex v s))

/-- The log-16 encoding at `v` of coefficient lane `t` of a 256-vector. -/
def laneValue (m : Fin 256 → K) (v : Fin 65536) (t : Fin 4) : K :=
  AspisR1.RepeatedLift.secondLinear
    (AspisV5FriConcreteEncoderCommutation.coefficientLane 64 t m) v

/-- Encoding the α-folded 64 coefficients is the α-fold of the four lane
encodings (linearity of `secondLinear`). -/
theorem secondLinear_coefficientFold (alpha : K) (m : Fin 256 → K) (v : Fin 65536) :
    AspisR1.RepeatedLift.secondLinear
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha m) v =
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue alpha (laneValue m v) := by
  have hm : AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha m =
      AspisV5FriConcreteEncoderCommutation.coefficientLane 64 0 m +
        alpha • AspisV5FriConcreteEncoderCommutation.coefficientLane 64 1 m +
        alpha ^ 2 • AspisV5FriConcreteEncoderCommutation.coefficientLane 64 2 m +
        alpha ^ 3 • AspisV5FriConcreteEncoderCommutation.coefficientLane 64 3 m := by
    funext d
    simp only [AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer_apply,
      AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul,
      AspisV5FriConcreteEncoderCommutation.coefficientLane_apply]
  rw [hm]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    AspisV5ComponentCConcreteFoldLinearity.coefficientFoldValue, laneValue]

theorem lineNode_one (v : Fin 65536) : lineNode (K := K) v 1 = -lineNode v 0 := by
  unfold lineNode
  rw [AspisR1.RepeatedLift.storedFirstLineX18_slot1 v, map_neg]

theorem lineNode_three (v : Fin 65536) : lineNode (K := K) v 3 = -lineNode v 2 := by
  unfold lineNode
  rw [AspisR1.RepeatedLift.storedFirstLineX18_slot3 v, map_neg]

theorem lineNode_T2 (v : Fin 65536) :
    AspisCircleTensorBinding.doubledFactor (lineNode (K := K) v 2) 1 =
      -AspisCircleTensorBinding.doubledFactor (lineNode (K := K) v 0) 1 := by
  have h := congrArg (algebraMap (ZMod AspisCircleGroupOrder.P) K)
    (AspisR1.RepeatedLift.storedFirstLineX18_slot2_T2 v)
  rw [AspisR1.RepeatedLift.doubledFactor_map, map_neg,
    AspisR1.RepeatedLift.doubledFactor_map] at h
  exact h

/-- Distinct children of one parent have distinct embedded nodes
(injectivity of the stored line-18 domain). -/
theorem lineNode_injective (v : Fin 65536) {s t : Fin 4}
    (h : lineNode (K := K) v s = lineNode v t) : s = t := by
  unfold lineNode at h
  have h1 := FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K h
  have h2 := AspisV7ExactOneFoldDomains.storedFirstLineX18_injective h1
  have h3 := congrArg Fin.val h2
  simp only [AspisV5ComponentCConcreteFoldLinearity.childIndex_val] at h3
  exact Fin.ext (by omega)

theorem lineNode_zero_ne (v : Fin 65536) : lineNode (K := K) v 0 ≠ 0 := by
  intro h0
  have h : lineNode (K := K) v 1 = lineNode v 0 := by
    rw [lineNode_one, h0, neg_zero]
  exact absurd (lineNode_injective v h) (by decide)

theorem lineNode_two_ne (v : Fin 65536) : lineNode (K := K) v 2 ≠ 0 := by
  intro h0
  have h : lineNode (K := K) v 3 = lineNode v 2 := by
    rw [lineNode_three, h0, neg_zero]
  exact absurd (lineNode_injective v h) (by decide)

theorem lineNode_T2_ne (v : Fin 65536) :
    AspisCircleTensorBinding.doubledFactor (lineNode (K := K) v 0) 1 ≠ 0 := by
  intro hD
  have hD2 : AspisCircleTensorBinding.doubledFactor (lineNode (K := K) v 2) 1 = 0 := by
    rw [lineNode_T2, hD, neg_zero]
  have e0 : 2 * lineNode (K := K) v 0 ^ 2 - 1 = 0 := hD
  have e2 : 2 * lineNode (K := K) v 2 ^ 2 - 1 = 0 := hD2
  have e : (lineNode (K := K) v 0 - lineNode v 2) * (lineNode v 0 + lineNode v 2) * 2 =
      (2 * lineNode (K := K) v 0 ^ 2 - 1) - (2 * lineNode v 2 ^ 2 - 1) := by ring
  rw [e0, e2, sub_zero] at e
  rcases mul_eq_zero.mp e with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (lineNode_injective v (sub_eq_zero.mp h')) (by decide)
    · have h12 : lineNode (K := K) v 1 = lineNode v 2 := by
        rw [lineNode_one, eq_neg_of_add_eq_zero_left h', neg_neg]
      exact absurd (lineNode_injective v h12) (by decide)
  · exact AspisWide.InitialEncoder.two_ne_zero h

/-! The three table entries, embedded.  Proved by explicit rewriting
(`two_mul`, ring-hom laws); no numeral of `ZMod P` is evaluated. -/

theorem lineInverse_zero_map (v : Fin 65536) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 0) =
      (2 * lineNode (K := K) v 0)⁻¹ := by
  change algebraMap (ZMod AspisCircleGroupOrder.P) K ((2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0))⁻¹) = _
  rw [map_inv₀, two_mul (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0)), map_add,
    ← two_mul (algebraMap (ZMod AspisCircleGroupOrder.P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0)))]
  rfl

theorem lineInverse_one_map (v : Fin 65536) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 1) =
      -(2 * lineNode (K := K) v 3)⁻¹ := by
  change algebraMap (ZMod AspisCircleGroupOrder.P) K (-(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3))⁻¹) = _
  rw [map_neg, map_inv₀, two_mul (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3)), map_add,
    ← two_mul (algebraMap (ZMod AspisCircleGroupOrder.P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 3)))]
  rfl

theorem lineInverse_two_map (v : Fin 65536) :
    algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 2) =
      (2 * AspisCircleTensorBinding.doubledFactor (lineNode (K := K) v 0) 1)⁻¹ := by
  change algebraMap (ZMod AspisCircleGroupOrder.P) K ((2 * (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1))⁻¹) = _
  rw [map_inv₀, two_mul (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2 - 1), map_add, map_sub, map_one,
    two_mul (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0) ^ 2), map_add, map_pow,
    ← two_mul (algebraMap (ZMod AspisCircleGroupOrder.P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0)) ^ 2),
    ← two_mul (2 * algebraMap (ZMod AspisCircleGroupOrder.P) K (AspisV7ExactOneFoldDomains.storedFirstLineX18 (AspisV5ComponentCConcreteFoldLinearity.childIndex v 0)) ^ 2 - 1)]
  rfl

/-- L_u (one parent): the line fold of the four stored children of `v`, with
the public inverse table, equals the log-16 encoding at `v` of the α₁-folded
256-coefficient message.  Holds for every `m` and every `α₁`. -/
theorem line_identity (alpha1 : K) (m : Fin 256 → K) (v : Fin 65536) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha1
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 0))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 1))
        (algebraMap (ZMod AspisCircleGroupOrder.P) K (lineInverse v 2))
        (fun s => AspisWide.FinalEncoder.exactFinalLinear m
          (AspisV5ComponentCConcreteFoldLinearity.childIndex v s)) =
      AspisR1.RepeatedLift.secondLinear
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha1 m) v := by
  have hsplit (s : Fin 4) :
      AspisWide.FinalEncoder.exactFinalLinear m
          (AspisV5ComponentCConcreteFoldLinearity.childIndex v s) =
        laneValue m v 0 + lineNode v s * laneValue m v 1 +
          AspisCircleTensorBinding.doubledFactor (lineNode v s) 1 * laneValue m v 2 +
          lineNode v s * AspisCircleTensorBinding.doubledFactor (lineNode v s) 1 *
            laneValue m v 3 :=
    AspisR1.RepeatedLift.exactFinalLinear_child_split m v s
  simp only [hsplit]
  rw [secondLinear_coefficientFold]
  exact lineFold_quartet AspisWide.InitialEncoder.two_ne_zero alpha1 (lineNode v)
    (laneValue m v) (lineNode_one v) (lineNode_three v) (lineNode_T2 v)
    (lineNode_zero_ne v) (lineNode_two_ne v) (lineNode_T2_ne v) _ _ _
    (lineInverse_zero_map v) (lineInverse_one_map v) (lineInverse_two_map v)

/-- L_u for the whole layer: the 2^18 → 2^16 line fold of the folded word
equals the log-16 encoding of the final 64 coefficients. -/
theorem line_layer_identity (alpha1 : K) (m : Fin 256 → K) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer 65536 alpha1 lineInverse
        (AspisWide.FinalEncoder.exactFinalLinear m) =
      AspisR1.RepeatedLift.secondLinear
        (AspisV5ComponentCConcreteFoldLinearity.coefficientFoldLayer 64 alpha1 m) := by
  funext v
  rw [AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer_apply]
  exact line_identity alpha1 m v

end Encoders

#print axioms childIndex_bridge
#print axioms s2b_identity
#print axioms s1_identity
#print axioms dot_weightsOf
#print axioms s2a_identity
#print axioms lineFold_quartet
#print axioms circ_identity
#print axioms circ_zero_of_fibre_zero
#print axioms secondLinear_coefficientFold
#print axioms lineNode_injective
#print axioms lineNode_T2_ne
#print axioms line_identity
#print axioms line_layer_identity

end R1Z.BatchedAlgebra

end
