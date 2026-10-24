import CheckpointBytes5Writer

/-! Counterexample to unrestricted identification of the sparse reference with
the shipped polymorphic writer. This does NOT refute the S2 success-conditioned
port: that port must keep its reached S2/64-weight provenance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_WriterBoundary
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier

def shippedTag : aspis_r1_cost_probe.transport.CheckpointAbi2Variant → U8
  | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8

/-- The actually extracted reference root ignores Prepared.variant here. -/
theorem selector_tag (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize) :
    body_byte p a hp hu 8#usize = ok 2#u8 := by
  simp (disch := scalar_tac) [body_byte,Array.index_usize,Array.make,lift]

/-- The unrestricted all-variant installation equality is false, independently
of oracle, canonical fields, physical allocation or hash implementation. -/
theorem not_shipped_tag (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (variant : p.variant = .S1) :
    body_byte p a hp hu 8#usize ≠ ok (shippedTag p.variant) := by
  rw [selector_tag,variant]
  decide

/-- Header disagreement also applies to the D branch. -/
theorem not_shipped_d_tag (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (variant : p.variant = .D) :
    body_byte p a hp hu 8#usize ≠ ok (shippedTag p.variant) := by
  rw [selector_tag,variant]
  decide

#print axioms selector_tag
#print axioms not_shipped_tag
#print axioms not_shipped_d_tag
end AspisR1.Port3_WriterBoundary
end
