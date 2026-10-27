import Aeneas
set_option autoImplicit false
namespace AspisR1.JHi_RetypePairSuccess
open Aeneas Aeneas.Std Result
theorem source {A E F : Type} (body : Result A) (out : A)
    (run : (body >>= fun x=>ok (core.result.Result.Ok () : core.result.Result Unit E,x))=
      ok (.Ok (),out)) :
    (body >>= fun x=>ok (core.result.Result.Ok () : core.result.Result Unit F,x))=
      ok (.Ok (),out) := by
  cases h : body with
  | fail e => simp only [h,bind_tc_fail] at run;cases run
  | div => simp only [h,bind_tc_div] at run;cases run
  | ok value =>
    simp only [h,bind_tc_ok] at run ⊢
    cases run
    rfl
#print axioms source
end AspisR1.JHi_RetypePairSuccess
