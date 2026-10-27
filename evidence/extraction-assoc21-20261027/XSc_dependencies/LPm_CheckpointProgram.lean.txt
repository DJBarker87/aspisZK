import LPm_CheckpointBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointProgram
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytes5Inputs
open CheckpointBytesBlocks CheckpointBytesBody CheckpointBytesDigest CheckpointBytesDecodeC5
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local irreducible] sourceBody LPm_CheckpointBody.nativeBody

variable (p : Prepared) (a : Accumulator) (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)

def materialize (hp hu : Digest) : Slice U8 :=
  ⟨(LPm_CheckpointBody.nativeBody p a size qb hp hu).map u8,by
    rw [List.length_map,LPm_CheckpointBody.source_body p a size qb canonical next]
    simp only [sourceBody,List.length_ofFn]
    scalar_tac⟩

theorem materialize_eq (hp hu : Digest) :
    materialize p a size qb canonical next hp hu = bodySlice p a hp hu := by
  apply Subtype.ext
  change (LPm_CheckpointBody.nativeBody p a size qb hp hu).map u8 =
    (sourceBody p a hp hu).map u8
  exact congrArg (List.map u8)
    (LPm_CheckpointBody.source_body p a size qb canonical next hp hu)

def returned (hp hu hc : Digest) : Slice U8 :=
  ⟨(materialize p a size qb canonical next hp hu).val ++ hc.val,by
    simp only [materialize,List.length_append,List.length_map]
    rw [LPm_CheckpointBody.source_body p a size qb canonical next]
    simp only [sourceBody,List.length_ofFn,hc.property]
    scalar_tac⟩

theorem returned_eq (hp hu hc : Digest) :
    returned p a size qb canonical next hp hu hc = finish p a hp hu hc := by
  apply Subtype.ext
  change (materialize p a size qb canonical next hp hu).val ++ hc.val =
    (bodySlice p a hp hu).val ++ hc.val
  rw [materialize_eq]

/-- Source-shaped linear program: the first TWO replies determine the same
field inventory; that body's actual bytes determine the THIRD query and the
returned prefix. There is no independently chosen middle cut or output. -/
def native (proof public1 : Slice U8) : Code (Slice U8) := do
  let hp ← read (singletonParts proof)
  let hu ← read (singletonParts public1)
  let out := materialize p a size qb canonical next hp hu
  let hc ← read (checksumParts out)
  pure (returned p a size qb canonical next hp hu hc)

/-- Equality of reified programs includes the chronological attempted-read
schedule for ALL replies, not merely equal successful output bytes. Native
association is supplied by the frozen source partitions and local gates. -/
theorem program_eq (proof public1 : Slice U8) :
    native p a size qb canonical next proof public1 = writer p a proof public1 := by
  simp only [native,writer,materialize_eq,returned_eq]

theorem result_and_effects {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof public1 : Slice U8) (before : Log) :
    run D hash (native p a size qb canonical next proof public1) before =
      run D hash (writer p a proof public1) before := by
  rw [program_eq]

#print axioms materialize_eq
#print axioms returned_eq
#print axioms program_eq
#print axioms result_and_effects
end AspisR1.LPm_CheckpointProgram
end
