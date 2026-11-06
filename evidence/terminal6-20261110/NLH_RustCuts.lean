import NLH_FoldRust
set_option autoImplicit false
namespace AspisR1.NLH_RustCuts
open Aeneas Aeneas.Std Result
inductive Cuts {S E R : Type} (step : E → S → Result (core.result.Result S R)) :
 List E → S → Result (core.result.Result S R) → List E → Prop where
 | nil (s) : Cuts step [] s (ok (.Ok s)) []
 | next {e es s middle out log} : step e s=ok (.Ok middle) →
   Cuts step es middle out log → Cuts step (e::es) s out (e::log)
 | returned {e es s err} : step e s=ok (.Err err) →
   Cuts step (e::es) s (ok (.Err err)) [e]
 | failed {e es s err} : step e s=fail err →
   Cuts step (e::es) s (fail err) [e]
 | diverged {e es s} : step e s=div → Cuts step (e::es) s div [e]
theorem result {S E R : Type} {step : E → S → Result (core.result.Result S R)}
 {es : List E} {s : S} {out : Result (core.result.Result S R)} {log : List E}
 (cuts : Cuts step es s out log) : NLH_FoldRust.run step es s=out := by
 induction cuts with
 | nil => rfl
 | next h _ ih => simp only [NLH_FoldRust.run,h,bind_tc_ok,ih]
 | returned h => simp only [NLH_FoldRust.run,h,bind_tc_ok]
 | failed h => simp only [NLH_FoldRust.run,h,bind_tc_fail]
 | diverged h => simp only [NLH_FoldRust.run,h,bind_tc_div]
theorem attempted_prefix {S E R : Type} {step : E → S → Result (core.result.Result S R)}
 {es : List E} {s : S} {out : Result (core.result.Result S R)} {log : List E}
 (cuts : Cuts step es s out log) : log <+: es := by
 induction cuts with
 | nil => exact List.prefix_refl []
 | next _ _ ih =>
   obtain ⟨suffix,h⟩ := ih
   exact ⟨suffix,congrArg (List.cons _) h⟩
 | returned => exact ⟨_,rfl⟩
 | failed => exact ⟨_,rfl⟩
 | diverged => exact ⟨_,rfl⟩
#print axioms result
#print axioms attempted_prefix
end AspisR1.NLH_RustCuts
