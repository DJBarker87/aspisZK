import RPz8_F3S_Segments
set_option autoImplicit false
namespace AspisR1.F3S_TwoSegments
 theorem shape {A B : Type} (xs : List (A × B)) (a b : A)
    (h : xs.map Prod.fst=[a,b]) : ∃ x y,xs=[(a,x),(b,y)] := by
  cases xs with
  | nil => cases h
  | cons x xs =>
    cases xs with
    | nil => cases h
    | cons y rest =>
      cases rest with
      | cons z zs => cases h
      | nil =>
        simp only [List.map_cons,List.map_nil,List.cons.injEq] at h
        exact ⟨x.2,y.2,by cases x;cases y;simp_all⟩
#print axioms shape
end AspisR1.F3S_TwoSegments
