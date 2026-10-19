import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace AspisR1.GSActualListExpansionBound

variable {I M : Type} [DecidableEq I] [DecidableEq M]

/-- The literal Cartesian expansion performed by one runtime lane update,
before its distance filter and duplicate removal. -/
def laneExpansion (lane : I) (family : List (I → M)) (decoded : List M) : List (I → M) :=
  family.flatMap fun t => decoded.map (Function.update t lane)

theorem laneExpansion_length_le (lane : I) (family : List (I → M))
    (decoded : List M) :
    (laneExpansion lane family decoded).length ≤ family.length * decoded.length := by
  induction family with
  | nil => simp [laneExpansion]
  | cons t ts ih =>
      simp only [laneExpansion, List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      calc
        decoded.length + (laneExpansion lane ts decoded).length ≤
            decoded.length + ts.length * decoded.length := Nat.add_le_add_left ih _
        _ = (ts.length + 1) * decoded.length := by
          rw [Nat.add_mul, Nat.one_mul]
          omega

theorem laneExpansion_length_le_100_112 (lane : I) (family : List (I → M))
    (decoded : List M) (hfamily : family.length ≤ 100)
    (hdecoded : decoded.length ≤ 112) :
    (laneExpansion lane family decoded).length ≤ 11200 := by
  have h := laneExpansion_length_le lane family decoded
  calc
    (laneExpansion lane family decoded).length ≤ family.length * decoded.length := h
    _ ≤ 100 * 112 := Nat.mul_le_mul hfamily hdecoded
    _ = 11200 := rfl

theorem filterMap_length_le {α β : Type} (xs : List α) (f : α → Option β) :
    (xs.filterMap f).length ≤ xs.length := by
  exact List.length_filterMap_le f xs

theorem filter_length_le {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length ≤ xs.length := by
  exact List.length_filter_le p xs

#print axioms laneExpansion_length_le
#print axioms laneExpansion_length_le_100_112
#print axioms filterMap_length_le
#print axioms filter_length_le
end AspisR1.GSActualListExpansionBound
