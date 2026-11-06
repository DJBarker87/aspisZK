import NHZ_NativeAssociation
set_option autoImplicit false
namespace AspisR1.NLH_FoldCore
open Aeneas Aeneas.Std Result
/-- Local analogue of NHZ_DRIVER.Cuts for field-call events, whose payloads
are not hash syscall parts. The same state is passed to every continuation.
This is composition support, never a native-cut producer. -/
def run {S E : Type} (step : E → S → Result S) : List E → S → Result S
 | [], s => ok s
 | e::es, s => do let next ← step e s; run step es next
inductive Cuts {S E : Type} (step : E → S → Result S) :
 List E → S → Result S → List E → Prop where
 | nil (s) : Cuts step [] s (ok s) []
 | next {e es s middle out log} : step e s=ok middle →
   Cuts step es middle out log → Cuts step (e::es) s out (e::log)
 | failed {e es s error} : step e s=fail error →
   Cuts step (e::es) s (fail error) [e]
 | diverged {e es s} : step e s=div → Cuts step (e::es) s div [e]
theorem result {S E : Type} {step : E → S → Result S} {es : List E}
 {s : S} {out : Result S} {log : List E} (cuts : Cuts step es s out log) :
 run step es s=out := by
 induction cuts with
 | nil => rfl
 | next h _ ih => simp only [run,h,bind_tc_ok,ih]
 | failed h => simp only [run,h,bind_tc_fail]
 | diverged h => simp only [run,h,bind_tc_div]
theorem attempted_prefix {S E : Type} {step : E → S → Result S} {es : List E}
 {s : S} {out : Result S} {log : List E} (cuts : Cuts step es s out log) :
 log <+: es := by
 induction cuts with
 | nil => exact List.prefix_refl []
 | next _ _ ih =>
   obtain ⟨suffix,h⟩ := ih
   exact ⟨suffix,congrArg (List.cons _) h⟩
 | failed => exact ⟨_,rfl⟩
 | diverged => exact ⟨_,rfl⟩
#print axioms result
#print axioms attempted_prefix
end AspisR1.NLH_FoldCore
