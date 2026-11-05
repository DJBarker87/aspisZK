import NIW_AlignFinishInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishPrefix
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishExecution

def returning {A : Type} : Result (Reply A) → Prop
 | ok (.Ok _) => True
 | _ => False

def Continues : Event → Prop
 | .round _ _ _ _ outcome => returning outcome
 | .new _ outcome => returning outcome
 | .pair _ _ _ _ outcome => returning outcome
 | .dot _ _ outcome => returning outcome

inductive Prefix : List Event → Prop
 | nil : Prefix []
 | last (event : Event) : Prefix [event]
 | next (event : Event) (tail : List Event) (continues : Continues event)
   (history : Prefix tail) : Prefix (event::tail)

theorem observe_prefix {A B : Type} (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B)
 (continues : ∀ value,Continues (event (ok (.Ok value))))
 (tail : ∀ value,call=ok (.Ok value) → Prefix (next value).2) :
 Prefix (observe call event next).2 := by
 cases call with
 | fail err => exact .last _
 | div => exact .last _
 | ok reply =>
  cases reply with
  | Err err => exact .last _
  | Ok value => exact .next _ _ (continues value) (tail value rfl)

/-- An entered Err/fail/div event has no following child event. This covers
all source arms, including unreturned NEW/pair/dot calls, with no input domain
or successful-child premise. -/
theorem source (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) : Prefix (run r v p a).2 := by
 unfold run
 apply observe_prefix
 · intro value;trivial
 intro first firstCall
 apply observe_prefix
 · intro value;trivial
 intro claim claimCall
 apply observe_prefix
 · intro value;trivial
 intro owner newCall
 cases range : core.array.Array.index (core.ops.index.IndexSlice
  (core.slice.index.SliceIndexRangeToUsizeSlice FE)) p.alpha {«end»:=2#usize} with
 | fail err => exact .nil
 | div => exact .nil
 | ok alpha =>
  apply observe_prefix
  · intro value;trivial
  intro pair pairCall
  split
  · exact .nil
  · apply observe_prefix
    · intro value;trivial
    intro actual dotCall
    exact .nil

/-- The no-suffix meaning of Prefix, stated without any totality assumption. -/
theorem no_suffix (events : List Event) (history : Prefix events)
 (before : List Event) (event : Event) (after : List Event)
 (at_event : events=before++event::after) (aborted : ¬Continues event) : after=[] := by
 induction history generalizing before with
 | nil => cases before <;> cases at_event
 | last last =>
  cases before with
  | nil => cases at_event;rfl
  | cons head rest =>
   have impossible : 1=(rest.length+after.length)+2 := by
    have h := congrArg List.length at_event
    simp only [List.length_nil,List.length_singleton,List.length_append,List.length_cons] at h
    omega
   omega
 | next head tail continues history ih =>
  cases before with
  | nil => cases at_event;exact False.elim (aborted continues)
  | cons first rest =>
   have same := List.cons.inj at_event
   exact ih rest same.2

#print axioms observe_prefix
#print axioms source
#print axioms no_suffix
end AspisR1.NIW_AlignFinishPrefix
