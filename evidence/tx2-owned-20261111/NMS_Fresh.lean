import Aeneas
set_option autoImplicit false
namespace NMS_Fresh
/-- Fresh logical allocation names; runtime addresses may be reused. -/
def total : List Nat → Nat
 | [] => 0
 | x :: xs => x + total xs
def next (used : List Nat) : Nat := total used + 1
theorem member_le {x : Nat} {xs : List Nat} (member : x ∈ xs) : x ≤ total xs := by
 induction xs with
 | nil => cases member
 | cons a xs ih =>
  simp only [List.mem_cons] at member
  rcases member with same | rest
  · subst x
    simp only [total]
    omega
  · have bound := ih rest
    simp only [total]
    omega
theorem fresh (used : List Nat) : next used ∉ used := by
 intro member
 have bound := member_le member
 unfold next at bound
 omega
#print axioms member_le
#print axioms fresh
end NMS_Fresh
