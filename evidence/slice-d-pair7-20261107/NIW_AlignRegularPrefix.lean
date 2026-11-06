import NIW_AlignRegularPhaseSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularPrefix
open Aeneas Aeneas.Std Result NIT_Cuts NIT_PairControl NIW_AlignRegularStream

def Continues (event : Event) : Prop :=
 match event.outcome with | ok (.Ok _,_,_) => True | _ => False

inductive Prefix : List Event → Prop
 | nil : Prefix []
 | last (event : Event) : Prefix [event]
 | next (event : Event) (tail : List Event) (continues : Continues event)
   (history : Prefix tail) : Prefix (event::tail)

theorem from_ordered (ks : List Usize) (s : Scratch) (p : Parts) (events : List Event)
 (out : Result NHM_RegularKinds.Reply) (order : Ordered ks s p events out) : Prefix events := by
 induction order with
 | done s p => exact .nil
 | failed k ks s p err => exact .last _
 | diverged k ks s p => exact .last _
 | rejected k ks s after p post err => exact .last _
 | continued k ks s after p post events out tail ih => exact .next _ _ True.intro ih

theorem source [FIo_Native.Allocation] (c : Context) (before : Scratch) :
 Prefix (NIW_AlignRegularPhase.run c before).2.events := by
 rw [NIW_AlignRegularPhaseSource.events]
 exact from_ordered _ _ _ _ _ (NIW_AlignRegularInvocation.ordered c.w.value c.alpha.value.to_slice
  c.f.value c.ap0.value c.ap1.value _ before initial)

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

#print axioms from_ordered
#print axioms source
#print axioms no_suffix
end AspisR1.NIW_AlignRegularPrefix
