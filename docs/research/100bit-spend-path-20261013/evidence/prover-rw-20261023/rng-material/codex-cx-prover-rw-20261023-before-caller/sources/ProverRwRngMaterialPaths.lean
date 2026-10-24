import R1Z.ProverRwRngMaterialControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialPaths
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl
variable [TypeLeaves] [LocalLeaves]
abbrev Cells := alloc.vec.Vec aspis_statement.trace_v4.TraceCell
abbrev cellsReply := aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1
abbrev activeReply := pool_v1_pair_forest_copy_active_rows
abbrev Expander := SeedExpander
abbrev initial (hash : Hash) (seed : Array U8 32#usize) : Expander :=
  ⟨hash,seed,0#u64,Array.repeat 32#usize 0#u8,8#usize⟩

theorem material_reaches_layout (hash : Hash) (binding entropy : Array U8 32#usize)
    (c : Context) (cells : Cells) (active : Array Bool 1024#usize)
    (mask : c.mask_layout_fingerprint = PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    (factor : c.layout_factor_fingerprint = PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active)) :
    material hash binding c entropy =
      build_mask_material_for_layout AckStore hash binding c entropy (freshAck c)
        (alloc.vec.Vec.deref cells) active := by
  unfold material build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  simp only [cellsReply] at hcells
  simp only [activeReply] at hactive
  simp [mask,factor,hcells,hactive,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]

theorem material_zero_consumes (hash : Hash) (binding : Array U8 32#usize)
    (c : Context) (cells : Cells) (active : Array Bool 1024#usize)
    (mask : c.mask_layout_fingerprint = PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1)
    (factor : c.layout_factor_fingerprint = PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1)
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active)) :
    material hash binding c (Array.repeat 32#usize 0#u8) = .ok (.Err .ZeroPrivateEntropy,usedAck c) := by
  rw [material_reaches_layout hash binding _ c cells active mask factor hcells hactive]
  exact layout_zero_after_ack hash binding c _ active

/-- The first sampling component is an exact source cut, not a primitive
instruction or an assumed whole-material result. Its advanced expander is
retained in the premise; the emitted helper returns its acknowledged store. -/
theorem layout_sample_error (hash : Hash) (binding entropy seed : Array U8 32#usize)
    (c : Context) (encoded : Array U8 81#usize) (cells : Slice aspis_statement.trace_v4.TraceCell)
    (active : Array Bool 1024#usize) (inactive : Usize) (advanced : Expander) (e : BuildError)
    (nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 entropy
      (Array.repeat 32#usize 0#u8) = .ok false)
    (encode : StateOnlyHidingContext.encode c = .ok encoded)
    (hashed : hash (seedInput binding encoded entropy) = .ok seed)
    (hinactive : first_inactive_row active = .ok inactive)
    (sample : sample_mask_cells (initial hash seed) (Slice.len cells) = .ok (.Err e,advanced)) :
    build_mask_material_for_layout AckStore hash binding c entropy (freshAck c) cells active =
      .ok (.Err e,usedAck c) := by
  have ack := acknowledgment_fresh c
  change PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
    (freshAck c) c.statement_digest c.mask_nonce = _ at ack
  have derived := seed_derived hash binding entropy seed c encoded nonzero encode hashed
  simp only [initial] at sample
  simp [build_mask_material_for_layout,ack,derived,SeedExpander.new,hinactive,sample,
    core.result.Result.Insts.CoreOpsTry.branch]
  rfl

/-- Actual material fields are constructed from four ordered component
replies. There is no desired-material equality premise. -/
theorem layout_sample_success (hash : Hash) (binding entropy seed : Array U8 32#usize)
    (c : Context) (encoded : Array U8 81#usize) (cells : Slice aspis_statement.trace_v4.TraceCell)
    (active : Array Bool 1024#usize) (inactive : Usize) (s1 s2 s3 s4 : Expander)
    (c1 : alloc.vec.Vec aspis_core.field.M31)
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (g h1 : alloc.vec.Vec aspis_core.field.QM31)
    (nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 entropy
      (Array.repeat 32#usize 0#u8) = .ok false)
    (encode : StateOnlyHidingContext.encode c = .ok encoded)
    (hashed : hash (seedInput binding encoded entropy) = .ok seed)
    (hinactive : first_inactive_row active = .ok inactive)
    (hc1 : sample_mask_cells (initial hash seed) (Slice.len cells) = .ok (.Ok c1,s1))
    (hcolumns : sample_mask_columns s1 inactive active = .ok (.Ok columns,s2))
    (hg : sample_mask_g s2 inactive active = .ok (.Ok g,s3))
    (hh1 : sample_mask_h1_padding s3 inactive active = .ok (.Ok h1,s4)) :
    build_mask_material_for_layout AckStore hash binding c entropy (freshAck c) cells active =
      .ok (.Ok ⟨c1,columns,g,h1,c.mask_nonce⟩,usedAck c) := by
  have ack := acknowledgment_fresh c
  change PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
    (freshAck c) c.statement_digest c.mask_nonce = _ at ack
  have derived := seed_derived hash binding entropy seed c encoded nonzero encode hashed
  simp only [initial] at hc1
  simp [build_mask_material_for_layout,ack,derived,SeedExpander.new,hinactive,hc1,hcolumns,hg,hh1,
    core.result.Result.Insts.CoreOpsTry.branch]

#print axioms material_reaches_layout
#print axioms material_zero_consumes
#print axioms layout_sample_error
#print axioms layout_sample_success
end R1Z.ProverRwRngMaterialPaths
