import Wide.FinalEncoder
import WideTower

/-! F4 for the exact stored encoders. The fibre order is the production order
`(x,y), (x,-y), (-x,-y), (-x,y)`, indexed by `childIndex u s`.
No inverse-table correctness assumption is used. -/
set_option autoImplicit false
namespace AspisR0.Fold
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder
open AspisV5FriConcreteEncoderCommutation
open AspisV5ComponentCConcreteFoldLinearity
open AspisV7ExactOneFoldDomains AspisCircleGroupOrder
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

theorem fibre_coordinates_nonzero (u : Fin 262144) :
    exactCircleX (K := K) u ≠ 0 ∧ exactCircleY (K := K) u ≠ 0 := by
  have distinct (s t : Fin 4) (h :
      storedInitialCirclePoint20 (childIndex u s) =
        storedInitialCirclePoint20 (childIndex u t)) : s = t := by
    have hindex := storedInitialCirclePoint20_injective h
    simpa only [slotIndex_childIndex] using congrArg slotIndex hindex
  constructor
  · intro hz
    have hz' : X (storedInitialFibrePoint20 u) = 0 := by
      apply FaithfulSMul.algebraMap_injective (ZMod P) K
      simpa only [exactCircleX, map_zero] using hz
    have bad : (0 : Fin 4) = 3 := distinct 0 3 (by
      apply Subtype.ext
      apply Prod.ext
      · change X _ = X _
        rw [storedInitialCirclePoint20_x_slots, storedInitialCirclePoint20_x_slots]
        change X (storedInitialFibrePoint20 u) = -X (storedInitialFibrePoint20 u)
        rw [hz', neg_zero]
      · rw [storedInitialCirclePoint20_y_slots, storedInitialCirclePoint20_y_slots]
        rfl)
    exact (by decide : (0 : Fin 4) ≠ 3) bad
  · intro hz
    have hz' : (storedInitialFibrePoint20 u).1.2 = 0 := by
      apply FaithfulSMul.algebraMap_injective (ZMod P) K
      simpa only [exactCircleY, map_zero] using hz
    have bad : (0 : Fin 4) = 1 := distinct 0 1 (by
      apply Subtype.ext
      apply Prod.ext
      · change X _ = X _
        rw [storedInitialCirclePoint20_x_slots, storedInitialCirclePoint20_x_slots]
        rfl
      · rw [storedInitialCirclePoint20_y_slots, storedInitialCirclePoint20_y_slots]
        change (storedInitialFibrePoint20 u).1.2 = -(storedInitialFibrePoint20 u).1.2
        rw [hz', neg_zero])
    exact (by decide : (0 : Fin 4) ≠ 1) bad

def fibre (f : InitialWord K) (u : Fin 262144) (s : Fin 4) : K :=
  f (childIndex u s)

def fibreEvaluate (u : Fin 262144) : (Fin 4 → K) → (Fin 4 → K) :=
  radix4Evaluate (exactCircleY u) (-exactCircleY u) (exactCircleX u)

def fibreTransform (u : Fin 262144) : (Fin 4 → K) → (Fin 4 → K) :=
  radix4Decode (2 * exactCircleY u)⁻¹ (-(2 * exactCircleY u)⁻¹)
    (2 * exactCircleX u)⁻¹

def channels (f : InitialWord K) (s : Fin 4) (u : Fin 262144) : K :=
  fibreTransform u (fibre f u) s

def foldWord (alpha : K) (f : InitialWord K) : FinalWord K :=
  fun u => coefficientFoldValue alpha (fun s => channels f s u)

def foldMessage (alpha : K) (q : InitialMessage K) : FinalMessage K :=
  coefficientFoldLayer 256 alpha q

theorem fibre_inverse (u : Fin 262144) :
    Function.LeftInverse (fibreTransform (K := K) u) (fibreEvaluate u) ∧
      Function.RightInverse (fibreTransform (K := K) u) (fibreEvaluate u) := by
  obtain ⟨hx, hy⟩ := fibre_coordinates_nonzero (K := K) u
  have hxi : 2 * exactCircleX u * (2 * exactCircleX (K := K) u)⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero AspisWide.InitialEncoder.two_ne_zero hx)
  have hyi : 2 * exactCircleY u * (2 * exactCircleY (K := K) u)⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero AspisWide.InitialEncoder.two_ne_zero hy)
  have hnyi : 2 * -exactCircleY u * -(2 * exactCircleY (K := K) u)⁻¹ = 1 := by
    simpa only [mul_neg, neg_mul, neg_neg] using hyi
  exact ⟨radix4Decode_radix4Evaluate _ _ _ _ _ _ hyi hnyi hxi,
    radix4Evaluate_radix4Decode _ _ _ _ _ _ hyi hnyi hxi⟩

theorem encoded_fibre (q : InitialMessage K) (u : Fin 262144) :
    fibre (exactInitialEncoder q) u =
      fibreEvaluate u (fun s => exactFinalEncoder (coefficientLane 256 s q) u) := by
  rw [exactInitialEncoder_eq_circleLift]
  funext s
  exact radix4LiftEncoder_apply_child exactFinalLinear exactCircleY
    (-exactCircleY) exactCircleX q u s

theorem encoded_channels (q : InitialMessage K) (s : Fin 4) :
    channels (exactInitialEncoder q) s = exactFinalEncoder (coefficientLane 256 s q) := by
  funext u
  change fibreTransform u (fibre (exactInitialEncoder q) u) s = _
  rw [encoded_fibre, (fibre_inverse u).1]

theorem fold_encoded (alpha : K) (q : InitialMessage K) :
    foldWord alpha (exactInitialEncoder q) = exactFinalEncoder (foldMessage alpha q) := by
  funext u
  simp only [foldWord, encoded_channels]
  exact (encoder_coefficientFoldLayer_apply exactFinalLinear alpha q u).symm

/-- F4, including the channel identity and both directions of local inversion. -/
theorem F4 :
    (∀ (q : InitialMessage K) (s : Fin 4),
      channels (exactInitialEncoder q) s = exactFinalEncoder (coefficientLane 256 s q)) ∧
    (∀ (alpha : K) (q : InitialMessage K),
      foldWord alpha (exactInitialEncoder q) = exactFinalEncoder (foldMessage alpha q)) ∧
    (∀ u, Function.LeftInverse (fibreTransform (K := K) u) (fibreEvaluate u) ∧
      Function.RightInverse (fibreTransform (K := K) u) (fibreEvaluate u)) :=
  ⟨encoded_channels, fold_encoded, fibre_inverse⟩

theorem wideF4 : type_of% (@F4 AspisWideTower.WideExact _ _ (Classical.decEq _) _) :=
  @F4 AspisWideTower.WideExact _ _ (Classical.decEq _) _

#print axioms F4
#print axioms wideF4
end
end AspisR0.Fold
