import NHM_GroupDispatch
set_option autoImplicit false
namespace NHX_GroupPacket
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- S2 only: the exact same low tensor is forwarded to the CLOSED child.
The fallback is outside this packet's domain. No output-success premise. -/
theorem source (w : FIo_Native.weights.Weights) (f : Slice U8) (low : Array NE 16#usize)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) (size : f.val.length=2048) :
 FIo_Native.weights.grouped_inactive_pair w f low=NHM_GroupRoot.reference f low :=
 NHM_GroupDispatch.source w f low s2 size

theorem output (w : FIo_Native.weights.Weights) (f : Slice U8) (low : Array NE 16#usize)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) (size : f.val.length=2048)
 (hl : ∀ x∈low.val,canonE x) (out : NE)
 (run : FIo_Native.weights.grouped_inactive_pair w f low=ok out) : canonE out := by
 rw [NHI_GroupDispatch.source w f low s2 size] at run
 exact NHM_GroupRoot.canonical f low hl out run

#print axioms source
#print axioms output
end NHX_GroupPacket
