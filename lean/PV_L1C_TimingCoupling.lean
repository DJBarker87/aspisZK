import PV_L1C_TimingKey
/-! Extend the ORIGINAL L1 coupling and ORIGINAL charged event. No timing
constant, independent marginal coupling or new failure charge is introduced. -/
set_option autoImplicit false
namespace PV_L1C
open PV_RJ4IDB

/-- Given the other ordered channels and terminal state on the same good
samples, the exact remaining pathwise obligation is the retained timing word.
A stochastic runtime needs a coupling of its noise on this same carrier;
this theorem does not assume or construct that native noise coupling. -/
theorem timing_extension_iff {S A : Type}
 (real sim : S → NativeTrace A) (bad : S → Prop)
 (context : ∀ s, ¬bad s → (timingKey (real s)).1 = (timingKey (sim s)).1) :
 (∀ s, ¬bad s → real s = sim s) ↔
 (∀ s, ¬bad s → nativeTimes (real s).events = nativeTimes (sim s).events) := by
 constructor
 · intro h s hs; exact congrArg (fun t => nativeTimes t.events) (h s hs)
 · intro h s hs
   apply timing_key_injective
   exact Prod.ext (context s hs) (h s hs)

/-- Reusable directly as the `agree` argument of D163's dist_le_bad. This is
a MODEL implication, with both native association/coupling inputs still open. -/
theorem same_bad_event_agreement {S A : Type}
 (real sim : S → NativeTrace A) (bad : S → Prop)
 (context : ∀ s, ¬bad s → (timingKey (real s)).1 = (timingKey (sim s)).1)
 (times : ∀ s, ¬bad s → nativeTimes (real s).events = nativeTimes (sim s).events) :
 ∀ s, ¬bad s → nativeObservation (real s) = nativeObservation (sim s) := by
 intro s hs
 exact congrArg nativeObservation ((timing_extension_iff real sim bad context).mpr times s hs)

#print axioms timing_extension_iff
#print axioms same_bad_event_agreement
end PV_L1C
