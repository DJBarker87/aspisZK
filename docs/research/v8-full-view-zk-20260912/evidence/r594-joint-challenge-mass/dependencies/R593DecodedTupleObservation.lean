import AspisV8R19.R572SequentialWordMass
import AspisV8R19.R580SourceWordStream

set_option autoImplicit false
namespace AspisV8R19.R593DecodedTupleObservation
open MemoizedProgramLaw R572SequentialWordMass

private theorem map_fin_val_injective {p : Nat} :
    Function.Injective (List.map (Fin.val : Fin p → Nat)) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hxy,hrest⟩ := h
          have : x = y := Fin.val_injective hxy
          subst y
          exact congrArg (List.cons x) (ih hrest)

theorem decoded_tuple_observation {p : Nat} (target : List (Fin p))
    (v : View Nat (Option (Fin p)) (Option (List (Fin p)) × Nat)) :
    (if v.2.1.map (List.map Fin.val) = some (target.map Fin.val) then (1 : ℚ) else 0) =
      observedList target v := by
  cases hv : v.2.1 with
  | none => simp [observedList, hv]
  | some xs =>
      simp only [observedList, hv, Option.map_some, Option.some.injEq]
      by_cases h : xs = target
      · subst xs
        simp
      · have hmap : List.map Fin.val xs ≠ List.map Fin.val target := by
          intro e
          exact h (map_fin_val_injective e)
        simp [h, hmap]

#print axioms decoded_tuple_observation
end AspisV8R19.R593DecodedTupleObservation
