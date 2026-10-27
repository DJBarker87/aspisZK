import Aeneas
set_option autoImplicit false
namespace AspisR1.JHi_RetypeSuccess
open Aeneas Aeneas.Std Result
/-- Successful observations of one byte action do not depend on the unused
error carrier of an enclosing Result. Failure and divergence are preserved. -/
theorem source {A E F : Type} (body : Result A) (out : A)
    (run : (body >>= fun x=>ok (core.result.Result.Ok x : core.result.Result A E)) = ok (.Ok out)) :
    (body >>= fun x=>ok (core.result.Result.Ok x : core.result.Result A F)) = ok (.Ok out) := by
  cases h : body with
  | fail e => simp only [h,bind_tc_fail] at run;cases run
  | div => simp only [h,bind_tc_div] at run;cases run
  | ok value =>
    simp only [h,bind_tc_ok] at run ⊢
    cases run
    rfl
#print axioms source
end AspisR1.JHi_RetypeSuccess
