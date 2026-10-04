import AspisV8R19.R580SourceWordStream

set_option autoImplicit false
namespace AspisV8R19.R600ResultEvalLength
open R572SequentialWordMass R580SourceWordStream

theorem resultEval_limbs_success_length {p : Nat}
    (f : Nat → Option (Fin p)) (budget count cursor : Nat)
    (xs : List (Fin p)) (cursor' : Nat)
    (h : resultEval f (limbs budget count cursor) = (some xs, cursor')) :
    xs.length = count := by
  induction count generalizing cursor xs cursor' with
  | zero =>
      simp only [limbs, resultEval] at h
      have hx : xs = [] := by
        exact (Prod.mk.inj h).1 ▸ rfl
      simp [hx]
  | succ count ih =>
      rw [resultEval_limbs_succ] at h
      cases hf : resultEval f (scan budget cursor) with
      | mk head nextCursor =>
          cases head with
          | none => simp [hf] at h
          | some a =>
              cases ht : resultEval f (limbs budget count nextCursor) with
              | mk tail tailCursor =>
                  cases tail with
                  | none => simp [hf, ht, prependResult] at h
                  | some ys =>
                      simp [hf, ht, prependResult, Prod.mk.injEq] at h
                      obtain ⟨hxs, _⟩ := h
                      rw [hxs, List.length_cons, ih _ _ _ ht]

#print axioms resultEval_limbs_success_length
end AspisV8R19.R600ResultEvalLength
