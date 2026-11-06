import NLR_PrepareComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PreparePrefixBound
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open NLJ_Prepare
/-- Every source Result retains a nonempty entered occurrence prefix. -/
theorem nonempty (cfg : Configuration) {H : Type} {n : Nat} {s : State H}
 {out : Result Out} {log : AspisR1PublicPreparation.PreparedHashCode.Log} {events : List Event}
 (actual : Invocation cfg n s out log events) : events≠[] := by
 cases actual <;> simp only [List.cons_ne_nil,not_false_eq_true]
/-- Each entered source occurrence consumes one unit of the original fuel;
errors/divergence do not invent a suffix. No native schedule is inferred. -/
theorem length_bound (cfg : Configuration) {H : Type} {n : Nat} {s : State H}
 {out : Result Out} {log : AspisR1PublicPreparation.PreparedHashCode.Log} {events : List Event}
 (actual : Invocation cfg n s out log events) : events.length≤n := by
 induction actual with
 | returned head => simp only [List.length_cons,List.length_nil];omega
 | fail head => simp only [List.length_cons,List.length_nil];omega
 | div head => simp only [List.length_cons,List.length_nil];omega
 | next head tail ih => simp only [List.length_cons];omega
#print axioms nonempty
#print axioms length_bound
end AspisR1.NLR_PreparePrefixBound
end
