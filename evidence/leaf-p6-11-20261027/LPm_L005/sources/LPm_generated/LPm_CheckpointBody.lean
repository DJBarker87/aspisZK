import LPm_WeightLoop
import CheckpointBytes5Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointBody
open Aeneas Aeneas.Std Result
open CheckpointBytes5Writer CheckpointBytesBlocks CheckpointBytesBody
open CheckpointBytesDigest CheckpointBytesDecodeC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The fixed source field inventory is derived from the SAME p,a whose
weights the native iterator consumes. Neither a second inventory nor an
arbitrary middle checkpoint cut is accepted as an argument. -/
def nativeBody (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (hp hu : Digest) : Bytes :=
  CheckpointBytesBlocks.body (fields p a size qb) (stateOf hp) (stateOf hu)

/-- Existing raw field/selector proofs identify this single complete
inventory with the cohort selector; no caller output equality is assumed. -/
theorem source_body (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)
    (hp hu : Digest) :
    nativeBody p a size qb hp hu = sourceBody p a hp hu := by
  exact (body_c5 (fields p a size qb) canonical (stateOf hp) (stateOf hu)).trans
    (source_body_c5 p a hp hu size qb canonical next).symm

/-- The native weight traversal's final actual-carrier block is the last
block in that same inventory, by the LPi fold and actual finite indexing. -/
theorem weights_port (a : Accumulator) (size : a.weights.val.length = 64) :
    MultiproofConeCanonical.bytesOf
      (LPi_SerializationFold.fold [] a.weights.val) =
      rawKs (fun j : Fin 64 => a.weights.val[j.val]'(by rw [size]; exact j.isLt)) := by
  have index : (List.ofFn fun j : Fin 64 =>
      a.weights.val[j.val]'(by rw [size]; exact j.isLt)) = a.weights.val := by
    apply List.ext_getElem
    · simp [size]
    · intro i hi hj
      simp only [List.getElem_ofFn]
  rw [LPi_SerializationFold.contents,List.nil_append]
  unfold rawKs rawK MultiproofConeCanonical.bytesOf
  rw [index]
  simp only [List.map_flatMap]

#print axioms source_body
#print axioms weights_port
end AspisR1.LPm_CheckpointBody
end
