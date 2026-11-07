import NMT_345StepBase
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Composition rule for one actual `?` boundary, all outer and Rust Results. -/
theorem try_congr {A : Type} (r : Result (core.result.Result A PE))
 (f g : A → Result Ret) (next : ∀ a,f a = g a) : tryStep r f = tryStep r g := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok r =>
  cases r with
  | Err e => rfl
  | Ok a => exact next a
#print axioms try_congr
end NMT_345
