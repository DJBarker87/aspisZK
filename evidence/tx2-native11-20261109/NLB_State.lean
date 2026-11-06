import NKE_CommonEval
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result NKE_Free
/-- All nine source sites, including full replies. No second event vocabulary. -/
abbrev Event := NJU_CommonObserved.Event
/-- The continuation owns the entire caller frame. The chronological prefix is
carried by this same state; no independently supplied native log is consumed. -/
inductive State (A : Type) : Type 1 where
 | live (caller : Program Event A) (attempted : List Event)
 | done (result : Result A) (attempted : List Event)
 | invalid (attempted : List Event)

/-- Forward native-window fold. At a call, the codec exposes the actual site
arguments; the window supplies its full reply, and that reply alone selects the
continuation. A mismatching argument carrier is rejected, never repaired. -/
def G {A : Type} (window : Event → Event) (p : Program Event A)
 (before : List Event) : State A :=
 match p with
 | .ret value => .done (.ok value) before
 | .prim actual next =>
   match actual with
   | .ok value => G window (next value) before
   | .fail error => .done (.fail error) before
   | .div => .done .div before
 | .call codec seed next =>
   let event := window (codec.encode seed)
   let attempted := before ++ [event]
   match codec.decode event with
   | none => .invalid attempted
   | some (.ok value) => G window (next value) attempted
   | some (.fail error) => .done (.fail error) attempted
   | some .div => .done .div attempted
 termination_by structural p
end NLB_Parent
