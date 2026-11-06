import NLC_RankBase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Source slot initialization only. This says nothing about physical ownership,
canonicality, a successful child, or a native/source association. -/
def Ready {H : Type} (s : State H) : Prop :=
 (0 < rank s.next → s.locals.running.isSome = true) ∧
 (0 < rank s.next → s.locals.alpha.isSome = true) ∧
 (0 < rank s.next → s.locals.transcript.isSome = true) ∧
 (2 < rank s.next → s.locals.claims.isSome = true) ∧
 (4 < rank s.next → s.locals.terminalReply.isSome = true) ∧
 (5 < rank s.next → s.locals.terminal.isSome = true) ∧
 (7 < rank s.next → s.locals.low.isSome = true) ∧
 (8 < rank s.next → s.locals.high.isSome = true) ∧
 (9 < rank s.next → s.locals.blind.isSome = true) ∧
 (11 < rank s.next → s.locals.mask.isSome = true) ∧
 (12 < rank s.next → s.locals.record25.isSome = true) ∧
 (13 < rank s.next → s.locals.extra.isSome = true) ∧
 (14 < rank s.next → s.locals.product.isSome = true) ∧
 (15 < rank s.next → s.locals.partialValue.isSome = true) ∧
 (16 < rank s.next → s.locals.extraCell.isSome = true) ∧
 (17 < rank s.next → s.locals.masked.isSome = true) ∧
 (20 < rank s.next → s.locals.stateBefore.isSome = true) ∧
 (22 < rank s.next → s.locals.z0.isSome = true) ∧
 (23 < rank s.next → s.locals.record26.isSome = true) ∧
 (24 < rank s.next → s.locals.beforeZ1.isSome = true) ∧
 (26 < rank s.next → s.locals.z1.isSome = true) ∧
 (29 < rank s.next → s.locals.payload.isSome = true) ∧
 (30 < rank s.next → s.locals.root.isSome = true)

def ReadyPost {H : Type} : Post H → Prop
 | .inl _ => True
 | .inr after => Ready after

theorem ready_returned {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H)
 (initialized : ∀ a, Ready (put s e (store a))) : ReadyPost (returned s e r store) := by
 cases r with
 | Ok a => exact initialized a
 | Err e => trivial

def initial {H : Type} (input : Input H) : State H := {input:=input,locals:={},next:=.rounds}

theorem initial_ready {H : Type} (input : Input H) : Ready (initial input) := by
 simp [Ready,initial,rank]
#print axioms ready_returned
#print axioms initial_ready
end AspisR1.NLC_Finish
end
