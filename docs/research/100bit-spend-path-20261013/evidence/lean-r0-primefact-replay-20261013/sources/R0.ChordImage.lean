import R0.PolynomialPair
import R0.ChordDegree
import R0.Round
import R0.LinearDual

/-! Image and transpose pairing for the exact initial encoder. The image
is not enlarged to the ambient GRS code. -/
set_option autoImplicit false
namespace AspisR0.ChordImage
open Polynomial
open AspisR0.PolynomialPair AspisR0.ChordDegree AspisR0.RoundNormalization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriInitialCircleEncoderIdentity AspisV5ComponentCConcreteFoldLinearity
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV7ExactOneFoldDomains AspisCircleGroupOrder
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def domainX (i : Fin 1048576) : K := algebraMap (ZMod P) K (X (storedInitialCirclePoint20 i))
def domainY (i : Fin 1048576) : K := algebraMap (ZMod P) K (storedInitialCirclePoint20 i).1.2
def pairWord (p r : K[X]) : InitialWord K := fun i => p.eval (domainX i)+domainY i*r.eval (domainX i)
def lineWord (a b c : K) : InitialWord K := fun i => a+b*domainX i+c*domainY i
def code : Set (InitialWord K) := Set.range exactInitialEncoder

theorem domain_circle (i : Fin 1048576) : (domainX (K := K) i)^2+(domainY (K := K) i)^2=1 := by
  have h := congrArg (algebraMap (ZMod P) K) (storedInitialCirclePoint20 i).property
  simpa only [domainX, domainY, AspisCircleGroupOrder.X, map_add, map_pow, map_one] using h

theorem encoder_pair (q : InitialMessage K) : exactInitialEncoder q = pairWord (initialP0 q) (initialP1 q) := rfl

theorem pairWord_zero (p r : K[X]) (u : Fin 262144) :
    pairWord p r (childIndex u 0) = p.eval (exactCircleX u)+exactCircleY u*r.eval (exactCircleX u) := rfl

theorem pairWord_one (p r : K[X]) (u : Fin 262144) :
    pairWord p r (childIndex u 1) = p.eval (exactCircleX u)-exactCircleY u*r.eval (exactCircleX u) := by
  simp only [pairWord, domainX, domainY]
  rw [storedInitialCirclePoint20_x_slots, storedInitialCirclePoint20_y_slots]
  change p.eval (exactCircleX u)+algebraMap (ZMod P) K (-(storedInitialFibrePoint20 u).1.2)*r.eval (exactCircleX u) = _
  rw [map_neg]
  change _ + -exactCircleY u * _ = _
  ring

theorem pairWord_injective (p r s t : K[X])
    (hp : p.natDegree ≤ 513) (hr : r.natDegree ≤ 513)
    (hs : s.natDegree ≤ 513) (ht : t.natDegree ≤ 513)
    (same : pairWord p r = pairWord s t) : p = s ∧ r = t := by
  have evals (u : Fin 262144) : p.eval (exactCircleX u)=s.eval (exactCircleX u) ∧
      r.eval (exactCircleX u)=t.eval (exactCircleX u) := by
    have h0 := congrFun same (childIndex u 0)
    have h1 := congrFun same (childIndex u 1)
    rw [pairWord_zero, pairWord_zero] at h0
    rw [pairWord_one, pairWord_one] at h1
    constructor
    · apply mul_left_cancel₀ (AspisWide.InitialEncoder.two_ne_zero (K := K))
      linear_combination h0+h1
    · apply mul_left_cancel₀ (AspisR0.Fold.fibre_coordinates_nonzero u).2
      apply mul_left_cancel₀ (AspisWide.InitialEncoder.two_ne_zero (K := K))
      linear_combination h0-h1
  exact ⟨polynomial_eq_of_fibres p s hp hs (fun u => (evals u).1),
    polynomial_eq_of_fibres r t hr ht (fun u => (evals u).2)⟩

theorem product_word (a b c : K) (q : InitialMessage K) :
    pairWord (mulP0 a b c (initialP0 q) (initialP1 q))
      (mulP1 a b c (initialP0 q) (initialP1 q)) = lineWord a b c * exactInitialEncoder q := by
  funext i
  exact mul_eval a b c (domainX i) (domainY i) (initialP0 q) (initialP1 q) (domain_circle i)

def e1 : InitialMessage K →ₗ[K] K := (Polynomial.lcoeff K 511).comp p1Linear
def e2 (b c : K) : InitialMessage K →ₗ[K] K :=
  b • (Polynomial.lcoeff K 511).comp p0Linear - c • (Polynomial.lcoeff K 510).comp p1Linear

@[simp] theorem e1_apply (q : InitialMessage K) : e1 q = (initialP1 q).coeff 511 := by
  simp only [e1, LinearMap.comp_apply, p1Linear_apply, Polynomial.lcoeff_apply]
@[simp] theorem e2_apply (b c : K) (q : InitialMessage K) :
    e2 b c q = b*(initialP0 q).coeff 511-c*(initialP1 q).coeff 510 := by
  simp only [e2, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    p0Linear_apply, p1Linear_apply, Polynomial.lcoeff_apply, smul_eq_mul]

theorem image_iff (a b c : K) (hbc : b ≠ 0 ∨ c ≠ 0) (q : InitialMessage K) :
    lineWord a b c * exactInitialEncoder q ∈ code ↔ e1 q = 0 ∧ e2 b c q = 0 := by
  have hp : (initialP0 q).natDegree ≤ 511 := by have := initialP0_degree_lt q; omega
  have hr : (initialP1 q).natDegree ≤ 511 := by have := initialP1_degree_lt q; omega
  have bound := bounded_product_iff a b c (initialP0 q) (initialP1 q) hp hr hbc
  rw [e1_apply, e2_apply]
  rw [← bound]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨deg0,deg1⟩ := product_degree a b c (initialP0 q) (initialP1 q) hp hr
    have pairEq := pairWord_injective _ _ (initialP0 m) (initialP1 m) deg0 (by omega)
      (by have := initialP0_degree_lt m; omega) (by have := initialP1_degree_lt m; omega)
      ((product_word a b c q).trans hm.symm)
    rw [pairEq.1, pairEq.2]
    exact ⟨by have := initialP0_degree_lt m; omega, by have := initialP1_degree_lt m; omega⟩
  · rintro ⟨h0,h1⟩
    obtain ⟨m, hm0, hm1⟩ := pair_complete _ _ h0 h1
    refine ⟨m, ?_⟩
    rw [encoder_pair, hm0, hm1, product_word]

def chordMessage (a b c : K) (q : InitialMessage K) : InitialMessage K :=
  liftLinear (mulP0 a b c (initialP0 q) (initialP1 q), mulP1 a b c (initialP0 q) (initialP1 q))

theorem chordMessage_pair (a b c : K) (hbc : b ≠ 0 ∨ c ≠ 0) (q : InitialMessage K)
    (h1 : e1 q = 0) (h2 : e2 b c q = 0) :
    initialP0 (chordMessage a b c q) = mulP0 a b c (initialP0 q) (initialP1 q) ∧
    initialP1 (chordMessage a b c q) = mulP1 a b c (initialP0 q) (initialP1 q) := by
  have hp : (initialP0 q).natDegree ≤ 511 := by have := initialP0_degree_lt q; omega
  have hr : (initialP1 q).natDegree ≤ 511 := by have := initialP1_degree_lt q; omega
  rw [e1_apply] at h1
  rw [e2_apply] at h2
  obtain ⟨h0,hodd⟩ := (bounded_product_iff a b c _ _ hp hr hbc).mpr ⟨h1,h2⟩
  simpa only [chordMessage, liftLinear_apply] using lift_bounded _ _ h0 hodd

theorem chordMessage_encoder (a b c : K) (hbc : b ≠ 0 ∨ c ≠ 0) (q : InitialMessage K)
    (h1 : e1 q = 0) (h2 : e2 b c q = 0) :
    exactInitialEncoder (chordMessage a b c q) = lineWord a b c * exactInitialEncoder q := by
  obtain ⟨h0,hodd⟩ := chordMessage_pair a b c hbc q h1 h2
  rw [encoder_pair, h0, hodd, product_word]

/-- Multiplication by the line followed by truncation in the exact message
basis. On the kernel of the two image functionals no truncation occurs. -/
def chordLinear (a b c : K) : InitialMessage K →ₗ[K] InitialMessage K where
  toFun := chordMessage a b c
  map_add' q r := by
    change liftLinear (mulP0 a b c (initialP0 (q+r)) (initialP1 (q+r)),
      mulP1 a b c (initialP0 (q+r)) (initialP1 (q+r))) =
      liftLinear (mulP0 a b c (initialP0 q) (initialP1 q), mulP1 a b c (initialP0 q) (initialP1 q)) +
      liftLinear (mulP0 a b c (initialP0 r) (initialP1 r), mulP1 a b c (initialP0 r) (initialP1 r))
    rw [← map_add]
    apply congrArg (liftLinear (K := K))
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, p0_add, p1_add, mulP0, mulP1] <;> ring
  map_smul' k q := by
    change liftLinear (mulP0 a b c (initialP0 (k • q)) (initialP1 (k • q)),
      mulP1 a b c (initialP0 (k • q)) (initialP1 (k • q))) =
      k • liftLinear (mulP0 a b c (initialP0 q) (initialP1 q), mulP1 a b c (initialP0 q) (initialP1 q))
    rw [← map_smul]
    apply congrArg (liftLinear (K := K))
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, p0_smul, p1_smul, mulP0, mulP1, smul_eq_C_mul] <;> ring

def quotientWeights (a b c : K) (w : InitialMessage K) : InitialMessage K :=
  LinearDual.weights (chordLinear a b c) w

theorem quotient_pairing (a b c : K) (w q : InitialMessage K) :
    dot w (chordMessage a b c q) = dot (quotientWeights a b c w) q :=
  LinearDual.transpose_pairing (chordLinear a b c) w q

theorem image_pairing (a b c : K) (hbc : b ≠ 0 ∨ c ≠ 0)
    (w q m : InitialMessage K)
    (hm : exactInitialEncoder m = lineWord a b c * exactInitialEncoder q) :
    dot w m = dot (quotientWeights a b c w) q := by
  have he := (image_iff a b c hbc q).mp ⟨m, hm⟩
  have h := exactInitialEncoder_injective
    (hm.trans (chordMessage_encoder a b c hbc q he.1 he.2).symm)
  rw [h]
  exact quotient_pairing a b c w q

#print axioms image_pairing
#print axioms image_iff
#print axioms chordMessage_pair
#print axioms chordMessage_encoder
end
end AspisR0.ChordImage
