import NNE_HeapBytes
set_option autoImplicit false
noncomputable section
namespace NNE_Frame
open RSL
/-- Literally the payload part of TAS.Frame. The only supplied theorem is G2,
not a stage2/native=model equation, and no Root0 is required. -/
theorem image (s : SdkState) (o : Obs (Except ProgramError Unit × SdkState))
 (h : (∀ c b, Event.write c b ∉ o.events) ∧
  (∀ r s', o.exit = .ret (r,s') → ∀ i, (s'.cells i).payload = (s.cells i).payload))
 (heap : AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record))
 (before : NNE_HeapBytes.Image s heap)
 (r : Except ProgramError Unit) (post : SdkState)
 (returned : o.exit = .ret (r,post)) :
 NNE_HeapBytes.Image post heap ∧ ∀ c b, Event.write c b ∉ o.events := by
 refine ⟨?_,h.1⟩
 intro i
 exact (h.2 r post returned i).trans (before i)

/-- Returned errors are covered by the same G2 frame; an abort has no
invented post-state, while its entire observed event prefix remains write-free. -/
theorem event_prefix (s : SdkState) (o : Obs (Except ProgramError Unit × SdkState))
 (h : (∀ c b, Event.write c b ∉ o.events) ∧
  (∀ r s', o.exit = .ret (r,s') → ∀ i, (s'.cells i).payload = (s.cells i).payload))
 (pre tail : List Event) (split : o.events = pre ++ tail) :
 ∀ c b, Event.write c b ∉ pre := by
 intro c b hm
 apply h.1 c b
 rw [split]
 exact List.mem_append_left tail hm
#print axioms image
#print axioms event_prefix
end NNE_Frame
end
