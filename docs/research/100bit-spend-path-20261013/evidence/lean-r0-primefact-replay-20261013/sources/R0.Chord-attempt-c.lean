import R0.ChordImage
import R0.ChordGeometry

/-! A secant, a fixed linear interpolant, and the two exact-image conditions. -/
set_option autoImplicit false
namespace AspisR0.Chord
open Polynomial
open AspisR0.PolynomialPair AspisR0.ChordDegree AspisR0.ChordImage
open AspisR0.ChordGeometry AspisR0.RoundNormalization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriInitialCircleEncoderIdentity
open AspisWide.InitialEncoder AspisWide.Agreement
open AspisV7ExactOneFoldDomains AspisCircleGroupOrder
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def domainPoint (i : Fin 1048576) : Point K := ⟨(domainX i,domainY i),domain_circle i⟩
def BaseRational (z : Point K) : Prop :=
  z.1.1 ∈ Set.range (algebraMap (ZMod P) K) ∧ z.1.2 ∈ Set.range (algebraMap (ZMod P) K)

theorem domain_base (i : Fin 1048576) : BaseRational (domainPoint (K := K) i) :=
  ⟨⟨_,rfl⟩,⟨_,rfl⟩⟩

def L (z0 z1 : Point K) : InitialWord K :=
  lineWord (secantA z0 z1) (secantB z0 z1) (secantC z0 z1)

theorem no_domain_zero (z0 z1 : Point K) (hne : z0 ≠ z1)
    (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) (i : Fin 1048576) : L z0 z1 i ≠ 0 := by
  intro hz
  have he := secant_only_zeroes z0 z1 hne (domainPoint i) hz
  exact he.elim (fun h => h0 (h ▸ domain_base i)) (fun h => h1 (h ▸ domain_base i))

def evalMessage (q : InitialMessage K) (z : Point K) : K :=
  (initialP0 q).eval z.1.1 + z.1.2 * (initialP1 q).eval z.1.1

/-- Choose the first coordinate unless its endpoint difference is zero. -/
abbrev axisX (z0 z1 : Point K) : Prop := z1.1.1 ≠ z0.1.1
def axis (z0 z1 z : Point K) : K := if axisX z0 z1 then z.1.1 else z.1.2
def delta (z0 z1 : Point K) : K := axis z0 z1 z1-axis z0 z1 z0

theorem delta_ne_zero (z0 z1 : Point K) (hne : z0 ≠ z1) : delta z0 z1 ≠ 0 := by
  unfold delta axis
  split_ifs with hx
  · exact sub_ne_zero.mpr hx
  · apply sub_ne_zero.mpr
    intro hy
    apply hne
    exact Subtype.ext (Prod.ext (not_not.mp hx).symm hy.symm)

def interpolationPair (z0 z1 : Point K) (y : Fin 2 → K) : K[X] × K[X] :=
  let s := (y 1-y 0)/delta z0 z1
  if axisX z0 z1 then (C (y 0-s*z0.1.1)+C s*Polynomial.X,0)
  else (C (y 0-s*z0.1.2),C s)

theorem interpolation_degrees (z0 z1 : Point K) (y : Fin 2 → K) :
    (interpolationPair z0 z1 y).1.natDegree ≤ 511 ∧
    (interpolationPair z0 z1 y).2.natDegree ≤ 511 := by
  unfold interpolationPair
  split_ifs <;> dsimp <;> constructor <;> (try compute_degree) <;> omega

def interpolant (z0 z1 : Point K) (y : Fin 2 → K) : InitialMessage K :=
  liftLinear (interpolationPair z0 z1 y)

theorem interpolant_pair (z0 z1 : Point K) (y : Fin 2 → K) :
    initialP0 (interpolant z0 z1 y) = (interpolationPair z0 z1 y).1 ∧
    initialP1 (interpolant z0 z1 y) = (interpolationPair z0 z1 y).2 :=
  lift_bounded _ _ (interpolation_degrees z0 z1 y).1 (interpolation_degrees z0 z1 y).2

theorem interpolant_values (z0 z1 : Point K) (hne : z0 ≠ z1) (y : Fin 2 → K) :
    evalMessage (interpolant z0 z1 y) z0 = y 0 ∧ evalMessage (interpolant z0 z1 y) z1 = y 1 := by
  simp only [evalMessage, (interpolant_pair z0 z1 y).1, (interpolant_pair z0 z1 y).2]
  have hd := delta_ne_zero z0 z1 hne
  unfold interpolationPair
  split_ifs with hx
  · simp only [Prod.fst, Prod.snd, eval_add, eval_C, eval_mul, eval_X, eval_zero, mul_zero, add_zero]
    simp only [delta, axis, if_pos hx] at hd ⊢
    constructor <;> field_simp [hd] <;> ring
  · simp only [Prod.fst, Prod.snd, eval_C]
    simp only [delta, axis, if_neg hx] at hd ⊢
    constructor <;> field_simp [hd] <;> ring

def interpolationLinear (z0 z1 : Point K) : (Fin 2 → K) →ₗ[K] InitialMessage K where
  toFun := interpolant z0 z1
  map_add' y t := by
    change liftLinear (interpolationPair z0 z1 (y+t)) =
      liftLinear (interpolationPair z0 z1 y)+liftLinear (interpolationPair z0 z1 t)
    rw [← map_add]
    apply congrArg (liftLinear (K := K))
    unfold interpolationPair
    split_ifs <;> apply Prod.ext <;>
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, map_sub, map_mul, div_eq_mul_inv] <;> ring
  map_smul' k y := by
    change liftLinear (interpolationPair z0 z1 (k • y)) = k • liftLinear (interpolationPair z0 z1 y)
    rw [← map_smul]
    apply congrArg (liftLinear (K := K))
    unfold interpolationPair
    split_ifs <;> apply Prod.ext <;>
      simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd,
        smul_eq_C_mul, map_mul, map_sub, div_eq_mul_inv] <;> ring

theorem product_eval (z0 z1 : Point K) (hne : z0 ≠ z1) (q : InitialMessage K)
    (h1 : e1 q = 0) (h2 : e2 (secantB z0 z1) (secantC z0 z1) q = 0) (z : Point K) :
    evalMessage (chordMessage (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) q) z =
      secant z0 z1 z * evalMessage q z := by
  obtain ⟨h0,hodd⟩ := chordMessage_pair _ _ _ (secant_nontrivial z0 z1 hne) q h1 h2
  unfold evalMessage
  rw [h0, hodd]
  exact mul_eval (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) z.1.1 z.1.2
    (initialP0 q) (initialP1 q) z.property

/-- F6 for the exact image; the quotient weights are the transpose of the
line multiplication map in that same message basis. -/
theorem F6 (z0 z1 : Point K) (hne : z0 ≠ z1)
    (h0 : ¬ BaseRational z0) (h1 : ¬ BaseRational z1) :
    (∀ i, L z0 z1 i ≠ 0) ∧
    (∀ y, evalMessage (interpolant z0 z1 y) z0 = y 0 ∧
      evalMessage (interpolant z0 z1 y) z1 = y 1) ∧
    (∀ q, L z0 z1 * exactInitialEncoder q ∈ code ↔
      e1 q = 0 ∧ e2 (secantB z0 z1) (secantC z0 z1) q = 0) ∧
    (∀ w q m, exactInitialEncoder m = L z0 z1 * exactInitialEncoder q →
      dot w m = dot (quotientWeights (secantA z0 z1) (secantB z0 z1) (secantC z0 z1) w) q) :=
  ⟨no_domain_zero z0 z1 hne h0 h1, interpolant_values z0 z1 hne,
    image_iff _ _ _ (secant_nontrivial z0 z1 hne),
    image_pairing _ _ _ (secant_nontrivial z0 z1 hne)⟩

theorem wideF6 : type_of% (@F6 AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @F6 AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms F6
#print axioms wideF6
#print axioms interpolationLinear
#print axioms product_eval
end
end AspisR0.Chord
