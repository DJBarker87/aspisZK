import Std
set_option autoImplicit false
namespace XRw_GenericDriver
/-- The effect constructor includes its arbitrary error carrier (for example
Except E, or a three-way Result with failure and divergence). -/
def guarded {M : Type → Type} [Monad M] {S I : Type}
    (stage : S → I → M S) (stopped : S → Bool) (s : S) (i : I) : M S :=
  if stopped s then pure s else stage s i

def unrolled {M : Type → Type} [Monad M] {S I : Type}
    (stage : S → I → M S) (stopped : S → Bool) : List I → S → M S
  | [], s => pure s
  | i :: rest, s => if stopped s then pure s else do
      let next ← stage s i
      unrolled stage stopped rest next

/-- Whole effect equality: finish, error and selected state are preserved.
Only the pure/bind identity is needed; no stage success or totality premise. -/
theorem first_stop_fold {M : Type → Type} [Monad M] {S I O : Type}
    (pure_bind : ∀ (s : S) (k : S → M S), (pure s >>= k) = k s)
    (stage : S → I → M S) (stopped : S → Bool)
    (finish : S → M O) (indices : List I) (s : S) :
    (unrolled stage stopped indices s >>= finish) =
      (indices.foldlM (guarded stage stopped) s >>= finish) := by
  have hold : ∀ (is : List I) (s : S), stopped s = true →
      is.foldlM (guarded stage stopped) s = pure s := by
    intro is s hs
    induction is with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldlM_cons]
      change (guarded stage stopped s i >>= _) = _
      rw [show guarded stage stopped s i = pure s by simp only [guarded, hs, ↓reduceIte]]
      rw [pure_bind]
      exact ih
  have he : ∀ (is : List I) (s : S),
      unrolled stage stopped is s = is.foldlM (guarded stage stopped) s := by
    intro is
    induction is with
    | nil => intro s; rfl
    | cons i rest ih =>
      intro s
      by_cases hs : stopped s = true
      · rw [hold (i::rest) s hs]
        simp only [unrolled, hs, ↓reduceIte]
      · simp only [unrolled, guarded, hs, List.foldlM_cons]
        congr 1
        funext next
        exact ih next
  rw [he]
#print axioms first_stop_fold
end XRw_GenericDriver
