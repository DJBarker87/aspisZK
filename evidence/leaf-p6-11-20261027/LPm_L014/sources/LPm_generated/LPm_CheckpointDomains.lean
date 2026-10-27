import LPm_CheckpointTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointDomains
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytesBlocks CheckpointBytesBody
open CheckpointBytesDecodeC5 LPm_CheckpointTrace
attribute [local irreducible] sourceBody LPm_CheckpointBody.nativeBody

variable (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)

theorem body_length (hp hu : Digest) :
    (LPm_CheckpointBody.nativeBody p a size qb hp hu).length = 1736 := by
  rw [LPm_CheckpointBody.source_body p a size qb canonical next]
  simp only [sourceBody,List.length_ofFn]

theorem prefix_length (hp hu : Digest) :
    (prefixBlocks p a size qb hp hu).flatten.length = 712 := by
  have h := congrArg List.length (body_split p a size qb hp hu)
  rw [body_length p a size qb canonical next] at h
  simp only [List.length_append,MultiproofConeCanonical.bytesOf,List.length_map,
    LPi_SerializationFold.length,List.length_nil,size] at h
  omega

/-- Derive the native one-step writer precondition from the SAME prefix
trace. It is not an independently supplied 712-byte checkpoint buffer. -/
theorem reached_weight_prefix (hp hu hc : Digest) (body out : Slice U8)
    (tr : Trace p a size qb hp hu hc body out) : tr.beforeWeights.length = 712 := by
  have pre := append_result tr.prefixSteps
  simp only [List.nil_append] at pre
  rw [pre,← List.map_flatten,List.length_map]
  exact prefix_length p a size qb canonical next hp hu

/-- This single affine invariant covers the ten semantic fields, four
coordinates and 64 weights, all using the inherited arbitrary-prefix put_k
domain. No whole-buffer verifier loop is run. -/
theorem q_loop_domain (base n i : Nat) (endBound : base+16*n ≤ 1736) (active : i<n) :
    base+16*i ≤ 1720 ∧ base+16*(i+1) ≤ 1736 := by omega

theorem e_prefix_domain (at : Nat) (fits : at+32 ≤ 1736) : at ≤ 1704 := by omega

theorem query_prefix_domain (i : Nat) (active : i<22) :
    320+4*i ≤ 1732 ∧ 320+4*(i+1) ≤ 408 := by omega

#print axioms body_length
#print axioms prefix_length
#print axioms reached_weight_prefix
#print axioms q_loop_domain
#print axioms e_prefix_domain
#print axioms query_prefix_domain
end AspisR1.LPm_CheckpointDomains
end
