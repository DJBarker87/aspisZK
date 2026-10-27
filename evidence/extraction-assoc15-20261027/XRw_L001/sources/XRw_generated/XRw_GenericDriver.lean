import Std
set_option autoImplicit false
namespace XRw_GenericDriver
/-- The error carrier is arbitrary; divergence can be represented in it. -/
def guarded {E S I : Type} (stage : S → I → Except E S)
    (stopped : S → Bool) (s : S) (i : I) : Except E S :=
  if stopped s then .ok s else stage s i

def unrolled {E S I : Type} (stage : S → I → Except E S)
    (stopped : S → Bool) : List I → S → Except E S
  | [], s => .ok s
  | i :: rest, s => if stopped s then .ok s else do
      let next ← stage s i
      unrolled stage stopped rest next

/-- Whole Result equality, retaining the selected state and any error. Any
finish continuation can therefore be substituted, including an error mapper. -/
theorem first_stop_fold {E S I O : Type} (stage : S → I → Except E S)
    (stopped : S → Bool) (finish : S → Except E O) (indices : List I) (s : S) :
    (unrolled stage stopped indices s >>= finish) =
      (indices.foldlM (guarded stage stopped) s >>= finish) := by
  have hold : ∀ (is : List I) (s : S), stopped s = true →
      is.foldlM (guarded stage stopped) s = .ok s := by
    intro is s hs
    induction is with
    | nil => rfl
    | cons i rest ih => simpa only [List.foldlM_cons, guarded, hs, ↓reduceIte,
        Except.pure, Except.bind] using ih
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
      · simp only [unrolled, guarded, hs, ↓reduceIte, List.foldlM_cons]
        cases stage s i with
        | error e => rfl
        | ok next => exact ih next
  rw [he]
#print axioms first_stop_fold
end XRw_GenericDriver
