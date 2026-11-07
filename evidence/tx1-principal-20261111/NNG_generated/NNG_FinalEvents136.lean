import NNG_LIBEvents136
import NNG_NonUnit136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinalEvents136
open Aeneas Aeneas.Std Result

/-- Unit-returning marks are silent regardless of their literal tag. Every
other source call's reply type is proved non-Unit before reusing its effects. -/
def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event := by
  classical
  exact match event with
   | @NMT_CallTree.Event.call _ Reply _ _ _ => if Reply=Unit then [] else NNG_LIBEvents136.events env event

theorem unit {Args : Type} (env : RSL.Env) (site : String) (args : Args) (reply : Result Unit) :
    events env (.call site args reply) = [] := by simp [events]
#print axioms unit

theorem nonUnit {Args Reply : Type} (env : RSL.Env) (site : String) (args : Args) (reply : Result Reply)
    (different : Reply≠Unit) : events env (.call site args reply) = NNG_LIBEvents136.events env (.call site args reply) := by
  simp [events,different]
#print axioms nonUnit
end AspisR1.NNG_FinalEvents136
