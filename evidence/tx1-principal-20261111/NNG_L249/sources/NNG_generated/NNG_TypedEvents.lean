import NMT_CallTree
import RSL_Base
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TypedEvents
open Aeneas Aeneas.Std

/-- A deterministic effect decoder for one typed lexical occurrence. The
reply is retained by the typed trace; this selection reads only its exact
site and arguments. No effect is invented for a differently typed event. -/
def select {Args : Type} (site : String) (effects : Args → List RSL.Event)
    (event : NMT_CallTree.Event) : List RSL.Event := by
  classical
  exact match event with
    | @NMT_CallTree.Event.call A _ tag args _ =>
      if tag = site then
        if h : A = Args then effects (cast h args) else []
      else []

theorem same {Args Reply : Type} (site : String) (effects : Args → List RSL.Event)
    (args : Args) (reply : Result Reply) :
    select site effects (.call site args reply) = effects args := by
  simp [select]
#print axioms same

theorem other_site {Args Actual Reply : Type} (site tag : String) (effects : Args → List RSL.Event)
    (args : Actual) (reply : Result Reply) (different : tag ≠ site) :
    select site effects (.call tag args reply) = [] := by
  simp [select,different]
#print axioms other_site

theorem other_type {Args Actual Reply : Type} (site : String) (effects : Args → List RSL.Event)
    (args : Actual) (reply : Result Reply) (different : Actual ≠ Args) :
    select site effects (.call site args reply) = [] := by
  simp [select,different]
#print axioms other_type
end AspisR1.NNG_TypedEvents
