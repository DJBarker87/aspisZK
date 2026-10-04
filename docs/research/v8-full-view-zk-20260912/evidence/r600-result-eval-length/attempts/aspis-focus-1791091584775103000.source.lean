import AspisV8R19.R580SourceWordStream

set_option autoImplicit false
namespace AspisV8R19.R600ResultEvalLength
open R572SequentialWordMass R580SourceWordStream

theorem resultEval_limbs_length {p : Nat}
    (answer : Nat → Option (Fin p)) (budget count cursor : Nat)
    {xs : List (Fin p)} {next : Nat}
    (h : resultEval answer (limbs budget count cursor) = (some xs, next)) :
    xs.length = count := by
  induction count generalizing cursor xs next with
  | zero =>
      simp only [limbs, resultEval] at h
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      rcases h with ⟨hx, _⟩
      subst xs
      rfl
  | succ count ih =>
      rw [resultEval_limbs_succ] at h
      cases hf : resultEval answer (scan budget cursor) with
      | mk head nextCursor =>
          cases head with
          | none => simp [hf] at h
          | some a =>
              cases ht : resultEval answer (limbs budget count nextCursor) with
              | mk tail tailCursor =>
                  cases tail with
                  | none => simp [hf, ht, prependResult] at h
                  | some ys =>
                      simp [hf, ht, prependResult, Prod.mk.injEq] at h
                      obtain ⟨hxs, _⟩ := h
                      rw [← hxs, List.length_cons]
                      exact congrArg Nat.succ (ih nextCursor ht)

#print axioms resultEval_limbs_length
end AspisV8R19.R600ResultEvalLength
