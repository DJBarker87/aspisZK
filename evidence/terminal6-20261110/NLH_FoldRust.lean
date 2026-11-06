import NLH_FoldCore
set_option autoImplicit false
namespace AspisR1.NLH_FoldRust
open Aeneas Aeneas.Std Result
/-- Rust Err is a returned value, distinct from Aeneas fail/div. -/
def run {S E R : Type} (step : E → S → Result (core.result.Result S R)) :
 List E → S → Result (core.result.Result S R)
 | [],s => ok (.Ok s)
 | e::es,s => do
   let r ← step e s
   match r with
   | .Err err => ok (.Err err)
   | .Ok next => run step es next
theorem returned_error {S E R : Type} (step : E → S → Result (core.result.Result S R))
 (e : E) (es : List E) (s : S) (err : R) (h : step e s=ok (.Err err)) :
 run step (e::es) s=ok (.Err err) := by
 simp only [run,h,bind_tc_ok]
theorem failed {S E R : Type} (step : E → S → Result (core.result.Result S R))
 (e : E) (es : List E) (s : S) (err : Error) (h : step e s=fail err) :
 run step (e::es) s=fail err := by simp only [run,h,bind_tc_fail]
theorem diverged {S E R : Type} (step : E → S → Result (core.result.Result S R))
 (e : E) (es : List E) (s : S) (h : step e s=div) :
 run step (e::es) s=div := by simp only [run,h,bind_tc_div]
#print axioms returned_error
#print axioms failed
#print axioms diverged
end AspisR1.NLH_FoldRust
