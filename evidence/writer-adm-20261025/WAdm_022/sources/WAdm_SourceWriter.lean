import WAdm_BodyJoin
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_SourceWriter
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes5Effect CheckpointBytes3Namespaces CheckpointBytesDigest
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)

def toSlice (bs : Bytes) : Result (Slice U8) :=
  if h : bs.length ≤ Usize.max then
    ok ⟨bs.map CheckpointBytes5Writer.u8,by simpa only [List.length_map] using h⟩
  else fail .panic

/-- Explicit append-content writer. It retains proof/public/checksum order
and reads the checksum from the body just constructed. This is a content
interpretation; no native heap/allocator refinement is asserted here. -/
def code (p : Prepared) (a : Accumulator) (proof pub : Slice U8) : Code (Slice U8) := do
  let hp ← read (singletonParts proof)
  let hu ← read (singletonParts pub)
  let b := WAdm_SourceBody.body p a hp hu
  let buf ← liftResult (toSlice b)
  let hc ← read (checksumParts buf)
  liftResult (toSlice (b ++ bytesOf hc.val))

attribute [local irreducible] CheckpointBytesDecodeC5.sourceBody WAdm_SourceBody.body

theorem materialize (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    toSlice (WAdm_SourceBody.body p a hp hu) = ok (CheckpointBytes5Writer.bodySlice p a hp hu) := by
  rw [WAdm_BodyJoin.selector p a hp hu size qb canonical variant next]
  have size1 : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length = 1736 := by
    rw [CheckpointBytesDecodeC5.sourceBody,List.length_ofFn]
  have bound : (CheckpointBytesDecodeC5.sourceBody p a hp hu).length ≤ Usize.max := by
    rw [size1]
    scalar_tac
  simp only [toSlice,dif_pos bound,CheckpointBytes5Writer.bodySlice]

#print axioms materialize
end AspisR1.WAdm_SourceWriter
end
