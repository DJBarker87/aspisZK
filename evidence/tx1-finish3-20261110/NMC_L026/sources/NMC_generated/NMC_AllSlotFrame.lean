import NLU_SlotFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Slots
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Exact write permissions for EVERY optional parent slot; NLU's retained
frame covered only claims and alpha. No output array is supplied as a seed. -/
def LocalFrame {H : Type} (s : NLC_Finish.State H) (l : Locals H) : Prop :=
 ((s.next≠.rounds)→l.running=s.locals.running) ∧
 ((s.next≠.rounds)→l.alpha=s.locals.alpha) ∧
 ((s.next≠.rounds ∧ s.next≠.circle0 ∧ s.next≠.circle1)→l.transcript=s.locals.transcript) ∧
 ((s.next≠.claims)→l.claims=s.locals.claims) ∧
 ((s.next≠.terminal)→l.terminalReply=s.locals.terminalReply) ∧
 ((s.next≠.mapPublic)→l.terminal=s.locals.terminal) ∧
 ((s.next≠.lowArray)→l.low=s.locals.low) ∧
 ((s.next≠.highArray)→l.high=s.locals.high) ∧
 ((s.next≠.blind)→l.blind=s.locals.blind) ∧
 ((s.next≠.mask)→l.mask=s.locals.mask) ∧
 ((s.next≠.decode25)→l.extra=s.locals.extra) ∧
 ((s.next≠.multiply)→l.product=s.locals.product) ∧
 ((s.next≠.addMask)→l.partialValue=s.locals.partialValue) ∧
 ((s.next≠.addExtra)→l.masked=s.locals.masked) ∧
 ((s.next≠.stateBefore)→l.stateBefore=s.locals.stateBefore) ∧
 ((s.next≠.circle0)→l.z0=s.locals.z0) ∧
 ((s.next≠.decode26)→l.beforeZ1=s.locals.beforeZ1) ∧
 ((s.next≠.circle1)→l.z1=s.locals.z1) ∧
 ((s.next≠.record25a ∧ s.next≠.record25b)→l.record25=s.locals.record25) ∧
 ((s.next≠.record26a ∧ s.next≠.record26b)→l.record26=s.locals.record26) ∧
 ((s.next≠.payload2)→l.payload=s.locals.payload) ∧
 ((s.next≠.extra28)→l.extraCell=s.locals.extraCell) ∧
 ((s.next≠.rootCopy)→l.root=s.locals.root)
def PostFrame {H : Type} (s : NLC_Finish.State H) : NLC_Finish.Post H → Prop
 | .inl _=>True
 | .inr after=>LocalFrame s after.locals
theorem put {H : Type} (s : NLC_Finish.State H) (event : NLC_Finish.Event) (l : Locals H)
 (frame : LocalFrame s l) : PostFrame s (.inr (NLC_Finish.put s event l)) := frame
theorem next {H : Type} (s : NLC_Finish.State H) (event : NLC_Finish.Event) :
 PostFrame s (.inr (NLC_Finish.setNext s event)) := by simp [PostFrame,LocalFrame,NLC_Finish.setNext]
theorem returned {T H : Type} (s : NLC_Finish.State H) (event : NLC_Finish.Event)
 (reply : core.result.Result T r1_wire.Error) (store : T→Locals H)
 (frame : ∀ value,LocalFrame s (store value)) : PostFrame s (NLC_Finish.returned s event reply store) := by
 cases reply with
 | Ok value=>exact frame value
 | Err error=>trivial
#print axioms put
#print axioms next
#print axioms returned
end AspisR1.NMC_Slots
end
