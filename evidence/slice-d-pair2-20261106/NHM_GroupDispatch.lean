import NHI_GroupDispatch
import NHM_GroupRoot
set_option autoImplicit false
namespace NHM_GroupDispatch
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Exact SAME low tensor and full child Result on the S2 dispatch domain.
Outside this domain the frozen non-S2/wrong-size fallback is retained and
unqualified; native dispatch identity is still OPEN. -/
theorem source (w : FIo_Native.weights.Weights) (f : Slice U8) (low : Array NE 16#usize)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) (size : f.val.length=2048) :
 FIo_Native.weights.grouped_inactive_pair w f low=NHM_GroupRoot.reference f low := by
 rw [NHI_GroupDispatch.source w f low s2 size,NHM_GroupRoot.cohort]

#print axioms source
end NHM_GroupDispatch
