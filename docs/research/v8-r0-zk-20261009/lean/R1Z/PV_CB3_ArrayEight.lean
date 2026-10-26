import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_ArrayEight
open Aeneas Aeneas.Std
/-- Shape decomposition of every eight-word extracted array. -/
theorem view (rank : Array U32 8#usize) :
    ∃ a b c d e f g h : U32, rank = Array.make 8#usize [a,b,c,d,e,f,g,h] := by
  rcases rank with ⟨xs,hlen⟩
  cases xs with
  | nil => simp at hlen
  | cons a xs =>
    cases xs with
    | nil => simp at hlen
    | cons b xs =>
      cases xs with
      | nil => simp at hlen
      | cons c xs =>
        cases xs with
        | nil => simp at hlen
        | cons d xs =>
          cases xs with
          | nil => simp at hlen
          | cons e xs =>
            cases xs with
            | nil => simp at hlen
            | cons f xs =>
              cases xs with
              | nil => simp at hlen
              | cons g xs =>
                cases xs with
                | nil => simp at hlen
                | cons h xs =>
                  have hz : xs.length = 0 := by
                    simp only [List.length_cons] at hlen
                    change xs.length + 8 = 8 at hlen
                    omega
                  have he : xs = [] := List.length_eq_zero_iff.mp hz
                  subst xs
                  exact ⟨a,b,c,d,e,f,g,h,rfl⟩
#print axioms view
end R1Z.PV_CB3_ArrayEight
