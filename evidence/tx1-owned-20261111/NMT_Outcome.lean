import Aeneas
set_option autoImplicit false
noncomputable section
universe u
namespace AspisR1.NMT_Outcome
open Aeneas Aeneas.Std Result
/-- A stopped invocation has no post-abort world. Returned errors are returns. -/
inductive Exit (A World : Type) where
 | returned (value : A) (after : World)
 | failed (reason : Error)
 | diverged
structure Observation (A World : Type) (Event : Type u) where
 exit : Exit A World
 attempted : List Event
/-- Total producer: there is an observation for EVERY admitted original input.
This type cannot be inhabited by an empty relation. The concrete producer must
be fixed by the actual frozen emitted body before any row is a candidate. -/
abbrev Producer (Input A World : Type) (Event : Type u) := Input → World → Observation A World Event
def result {A World : Type} : Exit A World → Result A
 | .returned a _ => .ok a
 | .failed e => .fail e
 | .diverged => .div
def frame {A World : Type} (before : World) : Exit A World → Prop
 | .returned _ after => after=before
 | .failed _ => True
 | .diverged => True
def Matches {A World : Type} {Event : Type u} (before : World)
 (expected : Result A × List Event) (actual : Observation A World Event) : Prop :=
 result actual.exit=expected.1 ∧ actual.attempted=expected.2 ∧ frame before actual.exit
/-- Existence is required in addition to a relation's universal implication. -/
def Total {Input A World : Type} {Event : Type u}
 (relation : Input → World → Observation A World Event → Prop) : Prop :=
 ∀ input before, ∃ observation, relation input before observation
theorem empty_not_total {Input A World : Type} {Event : Type u} [Nonempty Input] [Nonempty World] :
 ¬ Total (fun (_ : Input) (_ : World) (_ : Observation A World Event) => False) := by
 intro h
 obtain ⟨i⟩ := ‹Nonempty Input›
 obtain ⟨w⟩ := ‹Nonempty World›
 obtain ⟨_,bad⟩ := h i w
 exact bad
theorem stopped_has_no_world {A World : Type} (before : World) (e : Error) :
 frame (A:=A) before (.failed e) := True.intro
theorem returned_frame {A World : Type} (before after : World) (value : A)
 (h : frame before (.returned value after)) : after=before := h
#print axioms empty_not_total
#print axioms stopped_has_no_world
#print axioms returned_frame
end AspisR1.NMT_Outcome
