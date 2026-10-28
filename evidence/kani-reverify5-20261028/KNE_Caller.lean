import LPm_CheckpointLeaf
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Caller
open Aeneas Aeneas.Std
open CheckpointBytes5Writer CheckpointBytes5Join CheckpointBytesBody CheckpointBytesBlocks

-- Unit34 is an inventory/proposed bridge, not a merged driver proof.
-- This is the ONE outstanding driver hypothesis, on reached calls only.
def DriverEstablishedDomain (Reached : Prepared → Accumulator → Prop) : Prop :=
  ∀ p a, Reached p a → ∃ pm am, S1S7S8StateProvenance p a pm am

structure WriterDomain (p : Prepared) (a : Accumulator) : Prop where
  variant : p.variant = .S2
  size : a.weights.val.length = 64
  queriesBound : ∀ j : Fin 22,
    (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144
  canonical : CanonicalFields (fields p a size queriesBound)
  next : a.next.val = 10

theorem every_reached_call (Reached : Prepared → Accumulator → Prop)
    (driver : DriverEstablishedDomain Reached) (p : Prepared) (a : Accumulator)
    (reached : Reached p a) : WriterDomain p a := by
  obtain ⟨pm,am,h⟩ := driver p a reached
  exact ⟨h.variant,h.size,h.queriesBound,h.canonical,h.next⟩

#print axioms every_reached_call
end AspisR1.KNE_Caller
end
