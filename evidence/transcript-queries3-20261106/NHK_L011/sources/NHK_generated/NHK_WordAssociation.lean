import NHB_Observation
import NHB_Domains
import NHK_ReferenceFold
set_option autoImplicit false
namespace AspisR1.NHK_WordAssociation
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody
abbrev State := NGQ_SamplerTrace.State

/-- Transcription of K053's scalar/window G with its arbitrary membership reply. -/
def G (s : State) (x : U32) (cursor : Nat) (reply : Bool) (j : Fin 22) : NHB_Reference.Fields :=
  let halted := decide (s.accepted_len.val=22 ∨ s.draws.val=64)
  {stop:=halted,candidate:=x,cursor:=cursor+1,
   length:=if halted || reply then s.accepted_len.val else s.accepted_len.val+1,
   draws:=if halted then s.draws.val else s.draws.val+1,
   word:=if !halted && !reply && decide (j.val=s.accepted_len.val) then x
     else NHB_Inactive.cell s.accepted j}

theorem substitute (s : State) (x : U32) (cursor : Nat) (reply : Bool)
    (value : reply = NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val)) :
    ∀ j, G s x cursor reply j = NHB_Reference.fields s x cursor j := by
  subst reply
  intro j
  rfl

/-- Child determinism transfers the model poststate to the SAME logged native
poststate. Only local output windows are supplied, never a whole caller result. -/
theorem logged_post (s nativeAfter modelAfter : State) (x : U32)
    (cursor last : Nat) (stop reply : Bool)
    (hlen : s.accepted_len.val<22) (hdraw : s.draws.val<64)
    (value : reply = NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val))
    (windows : ∀ j, NHB_Observation.observe nativeAfter x last stop j = G s x cursor reply j)
    (modelFrame : NGQ_SamplerStep.Frame s modelAfter x
      (NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val))) :
    stop=false ∧ last=cursor+1 ∧ nativeAfter=modelAfter := by
  have observed : NHB_Observation.Relation s nativeAfter x cursor last stop := by
    intro j
    exact (windows j).trans (substitute s x cursor reply value j)
  obtain ⟨hs,hc,frame⟩ := NHB_Observation.continuing_frame s nativeAfter x cursor last stop hlen hdraw observed
  exact ⟨hs,hc,NGQ_SamplerStep.unique frame modelFrame⟩

theorem stopped_post (s nativeAfter : State) (x : U32) (cursor last : Nat) (stop reply : Bool)
    (full : s.accepted_len.val=22 ∨ s.draws.val=64)
    (windows : ∀ j, NHB_Observation.observe nativeAfter x last stop j = G s x cursor reply j) :
    stop=true ∧ last=cursor+1 ∧ nativeAfter=s := by
  have halt : decide (s.accepted_len.val=22 ∨ s.draws.val=64)=true := by simp only [full,decide_true]
  have observed : NHB_Observation.Relation s nativeAfter x cursor last stop := by
    intro j
    have same : G s x cursor reply j = NHB_Reference.fields s x cursor j := by
      simp only [G,NHB_Reference.fields,halt,Bool.true_or,if_true,Bool.not_true,Bool.false_and,if_false]
      rfl
    exact (windows j).trans same
  exact NHB_Observation.stopped_state s nativeAfter x cursor last stop full observed

/-- Thread the source-order trace while retaining the physical cursor. -/
theorem records {xs : List U32} {s final : State} {stop : Option Bool}
    (trace : NGQ_SamplerTrace.Trace xs s final stop) (cursor : Nat) :
    ∃ last, NHB_WordTrace.Trace cursor xs s final last stop := by
  induction trace generalizing cursor with
  | exhausted s => exact ⟨cursor,.exhausted cursor s⟩
  | stopped x xs s full => exact ⟨cursor+1,.stopped cursor x xs s full⟩
  | continuing x xs s next final stop hlen hdraw member membership frame tail ih =>
    obtain ⟨last,rest⟩ := ih (cursor+1)
    have value : member = NHB_Membership.reference x (s.accepted.val.take s.accepted_len.val) :=
      membership.trans (NHB_Membership.prefix_membership x s).symm
    rw [value] at frame
    exact ⟨last,.continuing cursor x xs s next final last stop hlen hdraw frame rest⟩

/-- No successful-loop result is assumed: the complete local-state chain is
constructed from the bounded invariant, then associated with the source loop. -/
theorem construct (xs : List U32) (s : State)
    (good : validState s) (cursor : Nat) :
    ∃ final pending last, NHB_WordTrace.Trace cursor xs s final last pending ∧
      validState final ∧
      Query31ExplicitListLoop.scanListLoop xs s=ok (final,pending) := by
  obtain ⟨final,pending,trace,valid⟩ := NGQ_SamplerConstruct.construct xs s good
  obtain ⟨last,edges⟩ := records trace cursor
  exact ⟨final,pending,last,edges,valid,NHB_WordTrace.source edges⟩

#print axioms substitute
#print axioms logged_post
#print axioms stopped_post
#print axioms records
#print axioms construct
end AspisR1.NHK_WordAssociation
