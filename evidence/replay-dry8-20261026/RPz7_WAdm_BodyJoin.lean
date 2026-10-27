import RPz7_WAdm_Append
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_BodyJoin
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytes3Namespaces CheckpointBytesDigest WAdm_SourceBody
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical

attribute [local irreducible] CheckpointBytesE.rawBytes CheckpointBytesBlocks.rawK CheckpointBytesBlocks.rawKs

theorem raw_blocks (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    WAdm_SourceBody.body p a hp hu =
      CheckpointBytesBlocks.body (CheckpointBytesBody.fields p a size qb) (stateOf hp) (stateOf hu) := by
  unfold WAdm_SourceBody.body
  rw [variant,CheckpointBytesHeader.next_cast a.next next,WAdm_Append.roots,WAdm_Append.alpha,
    WAdm_SourceBody.queries p a size qb,WAdm_Append.coordinates p a size qb,
    WAdm_Append.scalars p.semantic_alpha.val (show p.semantic_alpha.val.length = 10 from p.semantic_alpha.property),
    WAdm_Append.scalars a.weights.val size]
  simp only [CheckpointBytesBlocks.body,CheckpointBytesBlocks.blocks,CheckpointBytesBody.fields,
    List.flatten_cons,List.flatten_nil,List.append_nil,bytes_stateOf,put,putK,tag]
  simp only [List.append_assoc]
  rfl

theorem selector (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CheckpointBytesBlocks.CanonicalFields (CheckpointBytesBody.fields p a size qb))
    (variant : p.variant = .S2) (next : a.next.val = 10) :
    WAdm_SourceBody.body p a hp hu = CheckpointBytesDecodeC5.sourceBody p a hp hu := by
  rw [raw_blocks p a hp hu size qb variant next,
    CheckpointBytesBlocks.body_c5 _ canonical,
    CheckpointBytesDecodeC5.source_body_c5 p a hp hu size qb canonical next]

#print axioms raw_blocks
#print axioms selector
end AspisR1.WAdm_BodyJoin
end
