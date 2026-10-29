import PV_L1C_TimingKey
import R0Z.AbsorptionLaw
import R0Z.LawTransport
/-! Required exact joint law on the existing finite coupling carrier.
No instance is asserted for native clocks. The D359 evidence decision and
native clock/formatting association remain OPEN, not theorem hypotheses
smuggled into the deployed privacy endpoint. -/
set_option autoImplicit false
noncomputable section
namespace PV_L1C
open PV_RJ4IDB R0Z
variable {S T V U A : Type} [Fintype S] [Fintype T]

theorem law_map (left : S → V) (right : T → V) (f : V → U)
 (h : EqualLaws left right) : EqualLaws (fun s => f (left s)) (fun t => f (right t)) := by
 classical
 intro u
 exact LawTransport.mean_eq_of_equalLaws left right
   (fun v => if f v = u then 1 else 0) h

def JointTimingLaw (real : S → NativeTrace A) (sim : T → NativeTrace A) : Prop :=
 EqualLaws (fun s => timingKey (real s)) (fun t => timingKey (sim t))

/-- Necessary and sufficient exact timing extension: every test of the ordered
context/terminal AND serialized times has the same expectation. Marginal time,
fixed instruction counts and equal mean latency are each insufficient. -/
theorem timing_law_iff_tests (real : S → NativeTrace A) (sim : T → NativeTrace A) :
 JointTimingLaw real sim ↔
 ∀ test : ((List NativeEvent × Terminal A) × List Bytes) → ℚ,
  mean (fun s => test (timingKey (real s))) =
  mean (fun t => test (timingKey (sim t))) := by
 classical
 constructor
 · intro h test
   exact LawTransport.mean_eq_of_equalLaws _ _ test h
 · intro h v
   simpa only [law] using h (fun k => if k = v then 1 else 0)

/-- This formalizes why the required extension is joint and keeps the original
failure coupling. It does not add a new bad-event allowance. -/
theorem full_law_iff_timing_law (real : S → NativeTrace A) (sim : T → NativeTrace A) :
 EqualLaws real sim ↔ JointTimingLaw real sim := by
 classical
 constructor
 · intro h; exact law_map real sim timingKey h
 · intro h v
   have hv := h (timingKey v)
   simpa only [law,timing_key_injective.eq_iff] using hv

#print axioms law_map
#print axioms timing_law_iff_tests
#print axioms full_law_iff_timing_law
end PV_L1C
