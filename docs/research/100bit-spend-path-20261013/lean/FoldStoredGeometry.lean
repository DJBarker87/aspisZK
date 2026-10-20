import R1Line18Geometry
import R1NaturalProjection

/-! Symbolic interpretation of core r0/domain.rs. The factored fast_domain
constant tables require a separate source/table refinement. No large finite
domain is enumerated here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldStoredGeometry
open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisV5FriBitReverse AspisV7ExactOneFoldDomains
open AspisV5FriReleasedLineGeometry

/-- Mathematical exponent specified by r0/domain.rs:68–75. -/
def sourceFibre (u : Fin 262144) : C :=
  g ^ (1024 + 4096 * (reverseBits 18 u.val : Int))

def sourceX18 (u : Fin 262144) : ZMod P :=
  2 * X (sourceFibre u) ^ 2 - 1

def sourceX16 (v : Fin 65536) : ZMod P :=
  doubledFactor (sourceX18 (AspisR1.childIndex v 0)) 2

theorem fibre_eq_stored (u : Fin 262144) :
    sourceFibre u = storedInitialFibrePoint20 u := by
  rw [storedInitialFibrePoint20_eq_zpow]
  unfold sourceFibre AspisV6EncoderDistance.initialCircleExponent
  rw [storedInitialNaturalIndex20_child_zero]
  apply congrArg (fun n : Int => g ^ n)
  change 1024 + 4096 * (reverseBits 18 u.val : Int) =
    2 ^ 10 * (2 * ((2 * (reverseBits 18 u.val) : Nat) : Int) + 1)
  push_cast
  ring

theorem x18_eq_stored (u : Fin 262144) :
    sourceX18 u = storedFirstLineX18 u := by
  rw [storedFirstLineX18_eq_doubled, ← fibre_eq_stored]
  rfl

/-- Source and model child indices coincide for both the circle and line. -/
theorem child_eq_model {n : Nat} (u : Fin n) (s : Fin 4) :
    AspisR1.childIndex u s =
      AspisV5ComponentCConcreteFoldLinearity.childIndex u s := rfl

theorem query_parent_slot (u : Fin 262144) :
    4 * (u.val / 4) + u.val % 4 = u.val ∧
      u.val / 4 < 65536 ∧ u.val / 4 * 4 + 3 < 262144 := by
  have h := u.isLt
  omega

/-- Radix-four child reversal is symbolic in the parent, including the
rotation by the reversed low two bits. -/
theorem child_reversal (v : Fin 65536) (s : Fin 4) :
    reverseBits 18 (AspisR1.childIndex v s).val =
      reverseBits 16 v.val + 65536 * reverseBits 2 s.val := by
  exact reverseBits_childIndex 16 v.val s

/-- Quarter-turn exponent 2^29; slots reverse as [0,2,1,3]. -/
theorem child_rotation (v : Fin 65536) (s : Fin 4) :
    line18Point (reverseFin 18 (AspisR1.childIndex v s)) =
      g ^ (2048 + 8192 * (reverseBits 16 v.val : Int)) *
        g ^ (536870912 * (reverseBits 2 s.val : Int)) := by
  simp only [line18Point, reverseFin, Fin.val_mk, AspisR1.childIndex_val]
  rw [reverseBits_childIndex 16 v.val s]
  rw [← zpow_add]
  apply congrArg (fun n : Int => g ^ n)
  push_cast
  ring

theorem quartet (v : Fin 65536) (s : Fin 4) :
    sourceX18 (AspisR1.childIndex v s) =
      ![sourceX18 (AspisR1.childIndex v 0),
        -sourceX18 (AspisR1.childIndex v 0),
        sourceX18 (AspisR1.childIndex v 2),
        -sourceX18 (AspisR1.childIndex v 2)] s := by
  simp only [x18_eq_stored]
  exact storedLine18_child_slot v s

/-- Runtime y is slot 3, hence the negative of model x1 at slot 2. -/
theorem runtime_y (v : Fin 65536) :
    sourceX18 (AspisR1.childIndex v 3) =
      -sourceX18 (AspisR1.childIndex v 2) := by
  simp only [x18_eq_stored]
  exact storedLine18_slot3 v

theorem x16_eq_stored (v : Fin 65536) :
    sourceX16 v = storedLine16X v := by
  unfold sourceX16
  rw [x18_eq_stored]
  rw [show 2 = 1 + 1 from rfl,
    AspisV5FriNaturalBasisRadix4.doubledFactor_add, child_eq_model,
    storedLine18_t2_slot0, storedLine17_t2_binary]

/-- All four line children reach the same log-16 node after two doublings. -/
theorem quartet_t4 (v : Fin 65536) (s : Fin 4) :
    doubledFactor (sourceX18 (AspisR1.childIndex v s)) 2 =
      storedLine16X v := by
  have h0 := storedLine18_t2_slot0 v
  have h2 := storedLine18_t2_slot2 v
  have hp := storedLine17_t2_binary v
  have hneg (x : ZMod P) : doubledFactor (-x) 1 = doubledFactor x 1 := by
    simp only [doubledFactor, neg_sq]
  rw [x18_eq_stored, child_eq_model, storedLine18_child_slot,
    show 2 = 1 + 1 from rfl, AspisV5FriNaturalBasisRadix4.doubledFactor_add]
  fin_cases s <;>
    simp [AspisV5FriConcreteEncoderApplicability.radix4ChildPoint, hneg, h0, h2, hp]

#print axioms fibre_eq_stored
#print axioms x18_eq_stored
#print axioms child_eq_model
#print axioms query_parent_slot
#print axioms child_reversal
#print axioms child_rotation
#print axioms quartet
#print axioms runtime_y
#print axioms x16_eq_stored
#print axioms quartet_t4
end AspisR1.FoldStoredGeometry
