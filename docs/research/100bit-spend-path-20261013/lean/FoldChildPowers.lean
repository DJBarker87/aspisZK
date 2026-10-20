import FoldStoredGeometry

/-! The group-valued L1.3 statement, before taking x coordinates. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldChildPowers
open AspisCircleGroupOrder AspisV5FriBitReverse
open AspisV7ExactOneFoldDomains AspisV5FriReleasedLineGeometry

theorem line18Point_child_pow_four (v : Fin 65536) (s : Fin 4) :
    line18Point (reverseFin 18 (AspisR1.childIndex v s)) ^ 4 =
      line16Point (reverseFin 16 v) := by
  simp only [line18Point, line16Point, reverseFin, Fin.val_mk,
    AspisR1.childIndex_val]
  rw [reverseBits_childIndex 16 v.val s, ← zpow_natCast, ← zpow_mul]
  apply (g_zpow_eq_iff _ _).2
  rw [Int.modEq_iff_dvd]
  refine ⟨-(reverseBits 2 s.val : Int), ?_⟩
  push_cast
  ring

#print axioms line18Point_child_pow_four
end AspisR1.FoldChildPowers
