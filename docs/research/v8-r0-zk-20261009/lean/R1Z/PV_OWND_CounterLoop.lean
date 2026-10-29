import R1Z.PV_OWND_CounterBounds
import R1Z.PV_OWND_CounterOrder
set_option autoImplicit false
namespace R1Z.PV_OWND_CounterLoop
open PV_OWND_EndpointCounter PV_OWN_Link
/-- Two independent initialized counters stay in the u8 domain after every
successful prefix; this is a scalar law, not the native stack-array binding. -/
theorem bounds (xs : List Link) (p c p' c' : Counts)
 (h:check xs p c=.ok (p',c')) (hp:∀ i,p i≤2) (hc:∀ i,c i≤2) :
 (∀ i,p' i≤2) ∧ (∀ i,c' i≤2) := by
 induction xs generalizing p c with
 | nil =>
  simp only [check,Except.ok.injEq,Prod.mk.injEq] at h
  exact ⟨fun i=>h.1 ▸ hp i,fun i=>h.2 ▸ hc i⟩
 | cons v vs ih =>
  cases bp:bump p v.producer with
  | error e => rw [PV_OWND_CounterOrder.producer_error v vs p c e bp] at h;cases h
  | ok pp =>
   cases bc:bump c v.consumer with
   | error e => rw [PV_OWND_CounterOrder.consumer_error v vs p c pp e bp bc] at h;cases h
   | ok cc =>
    rw [PV_OWND_CounterOrder.success v vs p c pp cc bp bc] at h
    exact ih pp cc h (PV_OWND_CounterBounds.post_bound p pp v.producer bp hp)
     (PV_OWND_CounterBounds.post_bound c cc v.consumer bc hc)
#print axioms bounds
end R1Z.PV_OWND_CounterLoop
