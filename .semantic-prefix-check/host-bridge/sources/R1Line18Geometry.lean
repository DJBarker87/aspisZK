import AspisFormal.V5FriReleasedLineGeometry
import AspisFormal.V7ExactOneFoldDomains

set_option maxRecDepth 20000
set_option maxHeartbeats 200000
set_option autoImplicit false

/-!
# Radix-four geometry for the released stored log-18 line

This file proves the next line-domain geometry statement directly from the
stored line definitions and the bit-reversal identities.  It adds no decoder,
fold-soundness, or security premise.
-/

namespace AspisR1

open AspisCircleGroupOrder
open AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriBitReverse
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriExactLineDomains
open AspisV5FriReleasedLineGeometry
open AspisV7ExactOneFoldDomains

private theorem reverseBits18_child (i : Fin 65536) (slot : Fin 4) :
    reverseBits 18 (4 * (i : Nat) + slot) =
      reverseBits 16 i + 65536 * reverseBits 2 slot := by
  simpa using reverseBits_childIndex 16 (i : Nat) slot

private theorem reverseBits17_binary (i : Fin 65536) :
    reverseBits 17 (2 * (i : Nat)) = reverseBits 16 i := by
  simpa using reverseBits_two_mul 16 (i : Nat)

private theorem reverseBits17_binary_int (i : Fin 65536) :
    ((reverseBits 17 (2 * (i : Nat)) : Nat) : Int) = reverseBits 16 i :=
  congrArg (fun n : Nat => (n : Int)) (reverseBits17_binary i)

private theorem reverseBits2_zero :
    reverseBits 2 ((0 : Fin 4) : Nat) = 0 := by
  norm_num [reverseBits]

private theorem reverseBits2_one :
    reverseBits 2 ((1 : Fin 4) : Nat) = 2 := by
  norm_num [reverseBits]

private theorem reverseBits2_two :
    reverseBits 2 ((2 : Fin 4) : Nat) = 1 := by
  norm_num [reverseBits]

private theorem reverseBits2_three :
    reverseBits 2 ((3 : Fin 4) : Nat) = 3 := by
  norm_num [reverseBits]

theorem storedLine18_slot1 (i : Fin 65536) :
    storedFirstLineX18 (childIndex i 1) =
      -storedFirstLineX18 (childIndex i 0) := by
  unfold storedFirstLineX18 line18X line18Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits18_child i 1, reverseBits18_child i 0]
  rw [reverseBits2_one, reverseBits2_zero]
  push_cast
  simp only [add_zero]
  rw [show (2048 : Int) + 8192 * (reverseBits 16 i + 131072) =
      (2048 + 8192 * reverseBits 16 i) + (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact AspisV5FriExactLineDomains.X_zpow_add_halfTurn _

theorem storedLine18_slot3 (i : Fin 65536) :
    storedFirstLineX18 (childIndex i 3) =
      -storedFirstLineX18 (childIndex i 2) := by
  unfold storedFirstLineX18 line18X line18Point reverseFin
  simp only [childIndex_val]
  rw [reverseBits18_child i 3, reverseBits18_child i 2]
  rw [reverseBits2_three, reverseBits2_two]
  push_cast
  rw [show (2048 : Int) + 8192 * (reverseBits 16 i + 196608) =
      (2048 + 8192 * (reverseBits 16 i + 65536)) + (2 ^ 30 : Nat) by
    push_cast
    ring]
  exact AspisV5FriExactLineDomains.X_zpow_add_halfTurn _

theorem storedLine18_child_slot (i : Fin 65536) (slot : Fin 4) :
    storedFirstLineX18 (childIndex i slot) =
      radix4ChildPoint
        (storedFirstLineX18 (childIndex i 0))
        (storedFirstLineX18 (childIndex i 2)) slot := by
  fin_cases slot <;>
    simp [radix4ChildPoint, storedLine18_slot1, storedLine18_slot3]

private theorem storedLine18_sq_slot0 (i : Fin 65536) :
    line18Point (reverseFin 18 (childIndex i 0)) ^ 2 =
      storedLine17Point (binaryChildIndex i) := by
  unfold line18Point storedLine17Point line17Point
  rw [← zpow_natCast, ← zpow_mul]
  apply congrArg (fun z : Int => g ^ z)
  unfold reverseFin binaryChildIndex
  simp only [childIndex_val]
  rw [reverseBits18_child i 0, reverseBits17_binary i]
  rw [reverseBits2_zero]
  push_cast
  ring

private theorem storedLine17_binary_sq (i : Fin 65536) :
    storedLine17Point (binaryChildIndex i) ^ 2 =
      storedLine16Point i := by
  unfold storedLine17Point storedLine16Point line17Point line16Point
  rw [← zpow_natCast, ← zpow_mul]
  apply congrArg (fun z : Int => g ^ z)
  unfold reverseFin binaryChildIndex
  rw [reverseBits17_binary_int i]
  push_cast
  ring

theorem storedLine18_t2_slot0 (i : Fin 65536) :
    doubledFactor (storedFirstLineX18 (childIndex i 0)) 1 =
      storedLine17X (binaryChildIndex i) := by
  rw [show doubledFactor (storedFirstLineX18 (childIndex i 0)) 1 =
      X (line18Point (reverseFin 18 (childIndex i 0)) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine18_sq_slot0]
  rfl

theorem storedLine18_t2_slot2 (i : Fin 65536) :
    doubledFactor (storedFirstLineX18 (childIndex i 2)) 1 =
      -storedLine17X (binaryChildIndex i) := by
  rw [show doubledFactor (storedFirstLineX18 (childIndex i 2)) 1 =
      X (line18Point (reverseFin 18 (childIndex i 2)) ^ 2) by
    rw [X_sq]
    rfl]
  unfold line18Point storedLine17X storedLine17Point line17Point reverseFin
    binaryChildIndex
  simp only [childIndex_val]
  rw [← zpow_natCast, ← zpow_mul,
    reverseBits18_child i 2, reverseBits17_binary i]
  rw [reverseBits2_two]
  push_cast
  rw [show ((2048 : Int) + 8192 * (reverseBits 16 i + 65536)) * 2 =
      (4096 + 16384 * reverseBits 16 i) + (2 : Int) ^ 30 by
    push_cast
    ring]
  exact AspisV5FriExactLineDomains.X_zpow_add_halfTurn _

theorem storedLine17_t2_binary (i : Fin 65536) :
    doubledFactor (storedLine17X (binaryChildIndex i)) 1 =
      storedLine16X i := by
  rw [show doubledFactor (storedLine17X (binaryChildIndex i)) 1 =
      X (storedLine17Point (binaryChildIndex i) ^ 2) by
    rw [X_sq]
    rfl]
  rw [storedLine17_binary_sq]
  rfl

/-- Concrete radix-four geometry from the stored log-18 line to the stored
log-16 line.  The middle coordinate is the even-indexed stored log-17 point. -/
theorem storedLine18_radix4_geometry :
    Radix4LineGeometry
      storedFirstLineX18
      storedLine16X
      (fun i => storedFirstLineX18 (childIndex i 0))
      (fun i => storedFirstLineX18 (childIndex i 2))
      (fun i => storedLine17X (binaryChildIndex i)) where
  child_slot := storedLine18_child_slot
  t2_x0 := storedLine18_t2_slot0
  t2_x1 := storedLine18_t2_slot2
  t2_x2 := storedLine17_t2_binary

#print axioms storedLine18_radix4_geometry

private theorem map_radix4ChildPoint {K : Type*} [Field K]
    [Algebra (ZMod P) K] (x0 x1 : ZMod P) (slot : Fin 4) :
    algebraMap (ZMod P) K (radix4ChildPoint x0 x1 slot) =
      radix4ChildPoint
        (algebraMap (ZMod P) K x0) (algebraMap (ZMod P) K x1) slot := by
  fin_cases slot <;> simp [radix4ChildPoint, map_neg]

private theorem map_doubledFactor {K : Type*} [Field K]
    [Algebra (ZMod P) K] (x y : ZMod P)
    (h : doubledFactor x 1 = y) :
    doubledFactor (algebraMap (ZMod P) K x) 1 =
      algebraMap (ZMod P) K y := by
  have hm := congrArg (algebraMap (ZMod P) K) h
  simpa [doubledFactor, map_sub, map_mul, map_pow, map_one, map_ofNat] using hm

/-- The concrete log-18 to log-16 geometry remains valid after the released
base field is embedded in any field extension. -/
theorem storedLine18_radix4_geometry_algebraMap (K : Type*) [Field K]
    [Algebra (ZMod P) K] :
    Radix4LineGeometry
      (fun i => algebraMap (ZMod P) K (storedFirstLineX18 i))
      (fun i => algebraMap (ZMod P) K (storedLine16X i))
      (fun i => algebraMap (ZMod P) K
        (storedFirstLineX18 (childIndex i 0)))
      (fun i => algebraMap (ZMod P) K
        (storedFirstLineX18 (childIndex i 2)))
      (fun i => algebraMap (ZMod P) K
        (storedLine17X (binaryChildIndex i))) where
  child_slot := by
    intro i slot
    have h := congrArg (algebraMap (ZMod P) K)
      (storedLine18_child_slot i slot)
    simpa only [map_radix4ChildPoint] using h
  t2_x0 := by
    intro i
    exact map_doubledFactor (K := K)
      (storedFirstLineX18 (childIndex i 0))
      (storedLine17X (binaryChildIndex i)) (storedLine18_t2_slot0 i)
  t2_x1 := by
    intro i
    have hbase : doubledFactor (storedFirstLineX18 (childIndex i 2)) 1 =
        -storedLine17X (binaryChildIndex i) := storedLine18_t2_slot2 i
    have h := map_doubledFactor (K := K)
      (storedFirstLineX18 (childIndex i 2))
      (-storedLine17X (binaryChildIndex i)) hbase
    simpa only [map_neg] using h
  t2_x2 := by
    intro i
    exact map_doubledFactor (K := K)
      (storedLine17X (binaryChildIndex i)) (storedLine16X i)
      (storedLine17_t2_binary i)

#print axioms storedLine18_radix4_geometry_algebraMap

end AspisR1
