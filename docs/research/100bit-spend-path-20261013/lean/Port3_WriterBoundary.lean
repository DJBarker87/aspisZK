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
  simp (disch := scalar_tac) [body_byte,Array.index_usize,Array.make,lift,CheckpointBytesBodyArithmetic.sub_exact]

/-- The unrestricted all-variant installation equality is false, independently
of oracle, canonical fields, physical allocation or hash implementation. -/
theorem not_shipped_tag (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (variant : p.variant = .S1) :
    body_byte p a hp hu 8#usize ≠ ok (shippedTag p.variant) := by
  rw [selector_tag,variant]
  intro h
  have wrong := congrArg UScalar.val (Result.ok.inj h)
  change (2 : Nat) = 1 at wrong
  omega

/-- Header disagreement also applies to the D branch. -/
theorem not_shipped_d_tag (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (variant : p.variant = .D) :
    body_byte p a hp hu 8#usize ≠ ok (shippedTag p.variant) := by
  rw [selector_tag,variant]
  intro h
  have wrong := congrArg UScalar.val (Result.ok.inj h)
  change (2 : Nat) = 3 at wrong
  omega

def constantDigest : AspisR1Stage2.aspis_core.digest.Digest32 Unit where
  coremarkerCopyInst := {cloneInst := {clone := fun q => ok q}}
  digest := fun _ _ => ok (Array.repeat 32#usize 0#u8)

/-- The reference always materializes a fixed width, even with empty weights;
its selector failure fallback is an ordinary zero byte. -/
theorem reference_length (p : Prepared) (a : Accumulator) (hp hu hc : Array U8 32#usize) :
    (CheckpointBytes5Writer.finish p a hp hu hc).val.length = 1768 := by
  simp only [CheckpointBytes5Writer.finish,List.length_append,List.length_map,
    CheckpointBytesDecodeC5.sourceBody,List.length_ofFn,hc.property]
  rfl

theorem reference_total (p : Prepared) (a : Accumulator) (proof pub : Slice U8) :
    ∃ ck, CheckpointBytes5Effect.erase constantDigest ()
      (CheckpointBytes5Writer.writer p a proof pub) = ok ck ∧ ck.val.length = 1768 := by
  refine ⟨CheckpointBytes5Writer.finish p a (Array.repeat 32#usize 0#u8)
    (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8),?_,reference_length p a _ _ _⟩
  simp only [CheckpointBytes5Writer.writer,CheckpointBytes5Effect.erase_bind,
    CheckpointBytes5Effect.erase_read,CheckpointBytes5Effect.erase_pure,constantDigest,bind_tc_ok]

#print axioms reference_length
#print axioms reference_total

#print axioms selector_tag
#print axioms not_shipped_tag
#print axioms not_shipped_d_tag
end AspisR1.Port3_WriterBoundary
end
