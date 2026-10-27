import F3L_PreparedExt
import RPz7_F3L_WriterAlpha
import RPz7_F3L_WriterSemanticAlpha
import RPz7_F3L_WriterCoordinates
import RPz7_F3L_WriterRemaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_WriterPreparedEq
open AspisR1PublicPreparation
open F3K_CheckpointPreparedFields

/-- Complete raw-writer numeric interpretation. This does not yet identify
the source semantic fields/claim with F3's discovered model context. -/
theorem numeric (out : verifier.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (size : a.weights.val.length=64)
    (qb : ∀ j : Fin 22,((writerPrepared out).queries.val[j.val]'(by have h : (writerPrepared out).queries.val.length=22 := (writerPrepared out).queries.property;omega)).val<262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields (writerPrepared out) a size qb)) :
    CheckpointBytesBlocks.prepared (CheckpointBytesBody.fields (writerPrepared out) a size qb) canonical=
      F3L_SourcePrepared.numeric out := by
  have scalar := F3L_WriterPreparedScalar.fields out a size qb canonical
  have other := F3L_WriterRemaining.fields out a size qb canonical
  exact F3L_PreparedExt.fields _ _ scalar.2.2.2 other.1 scalar.1 scalar.2.1
    (F3L_WriterAlpha.alpha out a size qb canonical) scalar.2.2.1 other.2.1
    (F3L_WriterSemanticAlpha.semantic_alpha out a size qb canonical)
    (F3L_WriterCoordinates.coordinates out a size qb canonical) other.2.2

#print axioms numeric
end AspisR1.F3L_WriterPreparedEq
end
