import R1Z.PV_RDB2D_PV_B3P_Canonical133
namespace PV_B3P_Adjacent133
set_option autoImplicit false

def adjacent : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x::y::tail => if x == y then adjacent (y::tail) else x::adjacent (y::tail)

theorem members (xs : List Nat) (z : Nat) : z ∈ adjacent xs ↔ z ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    cases tail with
    | nil => rfl
    | cons y tail =>
      by_cases h : x = y
      · subst y
        simpa only [adjacent,beq_self_eq_true,↓reduceIte,List.mem_cons,or_self_left] using ih
      · simp only [adjacent,beq_iff_eq,h,↓reduceIte,List.mem_cons,ih]

theorem sorted (xs : List Nat) (hs : xs.Pairwise (· ≤ ·)) :
    (adjacent xs).Pairwise (· < ·) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x tail ih =>
    cases tail with
    | nil => exact List.pairwise_singleton _ _
    | cons y tail =>
      have ht := (List.pairwise_cons.mp hs).2
      have ih' := ih ht
      by_cases h : x = y
      · subst y
        simpa only [adjacent,beq_self_eq_true,↓reduceIte] using ih'
      · simp only [adjacent,beq_iff_eq,h,↓reduceIte]
        apply List.pairwise_cons.mpr
        refine ⟨?_,ih'⟩
        intro z hz
        have hxle : x ≤ y := (List.pairwise_cons.mp hs).1 y (by simp)
        have hxy : x < y := by omega
        have hzmem := (members (y::tail) z).mp hz
        rcases List.mem_cons.mp hzmem with rfl | hzmem
        · exact hxy
        · have hyz := (List.pairwise_cons.mp ht).1 z hzmem
          omega

theorem value (xs expected : List Nat) (hs : xs.Pairwise (· ≤ ·))
    (he : expected.Pairwise (· < ·)) (hm : ∀ z, z ∈ xs ↔ z ∈ expected) :
    adjacent xs = expected := by
  apply (sorted xs hs).eq_of_mem_iff he
  intro z
  exact (members xs z).trans (hm z)

#print axioms members
#print axioms sorted
#print axioms value
end PV_B3P_Adjacent133
