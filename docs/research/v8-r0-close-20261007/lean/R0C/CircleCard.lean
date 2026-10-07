import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy

/-! Cardinality of the split circle, proved symbolically via its nonzero
coordinate x+i*y. Instantiation at QM31 uses the tree's imaginary unit. -/
set_option autoImplicit false
namespace R0C.CircleCard
open AspisR0.ChordGeometry AspisCircleGroupOrder
open AspisV5ComponentCQM31TowerExact (QM31Exact)
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
noncomputable section
attribute [local instance] Classical.propDecidable

section Generic
variable {K : Type} [Field K] [Fintype K] [NeZero (2 : K)]
variable (i : K) (hi : i^2 = -1)

def coordinate (z : Point K) : K := z.val.1 + i*z.val.2

include hi in
omit [Fintype K] [NeZero (2 : K)] in
theorem coordinate_product (z : Point K) :
    coordinate i z * (z.val.1-i*z.val.2) = 1 := by
  calc
    _ = z.val.1^2-i^2*z.val.2^2 := by unfold coordinate; ring
    _ = 1 := by rw [hi]; linear_combination z.property

include hi in
omit [Fintype K] [NeZero (2 : K)] in
theorem coordinate_ne_zero (z : Point K) : coordinate i z ≠ 0 := by
  intro h
  have hp := coordinate_product i hi z
  rw [h, zero_mul] at hp
  exact zero_ne_one hp

include hi in
omit [Fintype K] in
theorem coordinate_injective : Function.Injective (coordinate i) := by
  intro z w he
  have hminus : z.val.1-i*z.val.2 = w.val.1-i*w.val.2 := by
    apply mul_left_cancel₀ (coordinate_ne_zero i hi w)
    rw [← he, coordinate_product i hi z, he, coordinate_product i hi w]
  have hii : i ≠ 0 := by intro h; simp [h] at hi
  have ht : (2 : K) ≠ 0 := NeZero.ne _
  apply Subtype.ext
  apply Prod.ext
  · apply mul_left_cancel₀ ht
    dsimp [coordinate] at he
    linear_combination he + hminus
  · apply mul_left_cancel₀ (mul_ne_zero ht hii)
    dsimp [coordinate] at he
    linear_combination he - hminus

def coordinateMap (z : Point K) : {t : K // t ≠ 0} :=
  ⟨coordinate i z, coordinate_ne_zero i hi z⟩

include hi in
omit [Fintype K] in
theorem coordinateMap_surjective : Function.Surjective (coordinateMap i hi) := by
  intro t
  have ht := t.property
  have htwo : (2 : K) ≠ 0 := NeZero.ne _
  let x : K := (t.val+t.val⁻¹)/2
  let y : K := -i*(t.val-t.val⁻¹)/2
  have hc : x^2+y^2=1 := by
    dsimp [x,y]
    field_simp
    linear_combination (t.val^2-1)^2 * hi
  refine ⟨⟨(x,y),hc⟩, ?_⟩
  apply Subtype.ext
  change x+i*y=t.val
  dsimp [x,y]
  field_simp
  linear_combination -(t.val^2-1)*hi

include hi in
theorem split_circle_card : Fintype.card (Point K) = Fintype.card K - 1 := by
  have he := Fintype.card_congr (Equiv.ofBijective (coordinateMap i hi)
    ⟨fun _ _ h => coordinate_injective i hi (congrArg Subtype.val h),
      coordinateMap_surjective i hi⟩)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at he
  exact he
include hi in
theorem split_circle_natCard : Nat.card (Point K) = Nat.card K - 1 := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact split_circle_card i hi
end Generic

local instance : NeZero (2 : QM31Exact) := ⟨AspisV8R15.ExactTowerChord.two_ne_zero⟩

/-- Nat.card avoids comparing the concrete subtype enumeration instances. -/
theorem qm31_circle_card : Nat.card (Point QM31Exact) = P^4-1 := by
  have hk : Nat.card QM31Exact = P^4 := by
    rw [Nat.card_eq_fintype_card]
    exact AspisV5ComponentCQM31TowerExact.qm31Exact_card
  exact (split_circle_natCard (K := QM31Exact) imaginaryUnit imaginary_square).trans
    (congrArg (fun n : Nat => n-1) hk)

#print axioms split_circle_card
#print axioms qm31_circle_card
end
end R0C.CircleCard
