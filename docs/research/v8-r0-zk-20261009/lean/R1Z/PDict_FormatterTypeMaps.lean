import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterTypeMaps
open Aeneas Aeneas.Std ProverRwFull
@[reducible] def types (base : ExternalTypes) (F : Type) : ExternalTypes :=
  {base with op27 := F}
abbrev Late := @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Trace := @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1
abbrev Compilation := @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev CopyLink := @aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1
abbrev Times := @aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes
abbrev Public := @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

def late (base : ExternalTypes) (F : Type) (x : @Late base) : @Late (types base F) :=
  @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.mk (types base F) (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.live_snapshot base x) (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.candidate_afterstate base x)

def unlate (base : ExternalTypes) (F : Type) (x : @Late (types base F)) : @Late base :=
  @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.mk base (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.live_snapshot (types base F) x) (@aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.candidate_afterstate (types base F) x)

def trace (base : ExternalTypes) (F : Type) (x : @Trace base) : @Trace (types base F) :=
  @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.mk (types base F) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.stable base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.late base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.variant base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.private_directions base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.value_bits base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.public_outputs base x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.afterstate base x)

def untrace (base : ExternalTypes) (F : Type) (x : @Trace (types base F)) : @Trace base :=
  @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.mk base (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.stable (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.late (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.variant (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.private_directions (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.value_bits (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.public_outputs (types base F) x) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1.afterstate (types base F) x)

def compilation (base : ExternalTypes) (F : Type) (x : @Compilation base) : @Compilation (types base F) :=
  @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.mk (types base F) (trace base F (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.trace base x)) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.semantic_c1 base x) (late base F (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.public_statement base x))

def uncompilation (base : ExternalTypes) (F : Type) (x : @Compilation (types base F)) : @Compilation base :=
  @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.mk base (untrace base F (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.trace (types base F) x)) (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.semantic_c1 (types base F) x) (unlate base F (@aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1.public_statement (types base F) x))

def link (base : ExternalTypes) (F : Type) (x : @CopyLink base) : @CopyLink (types base F) :=
  @aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.mk (types base F) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.id base x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.tag base x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.kind base x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.weight base x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.producer base x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.consumer base x)

def unlink (base : ExternalTypes) (F : Type) (x : @CopyLink (types base F)) : @CopyLink base :=
  @aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.mk base (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.id (types base F) x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.tag (types base F) x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.kind (types base F) x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.weight (types base F) x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.producer (types base F) x) (@aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1.consumer (types base F) x)

def times (base : ExternalTypes) (F : Type) (x : @Times base) : @Times (types base F) :=
  @aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.mk (types base F) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.public_data base x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.emit base x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.builders base x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.check base x)

def untimes (base : ExternalTypes) (F : Type) (x : @Times (types base F)) : @Times base :=
  @aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.mk base (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.public_data (types base F) x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.emit (types base F) x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.builders (types base F) x) (@aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes.check (types base F) x)

def pub (base : ExternalTypes) (F : Type) (x : @Public base) : @Public (types base F) := by
  cases x with
  | Transfer p l => exact @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer (types base F) p (late base F l)
  | Withdrawal p l => exact @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal (types base F) p (late base F l)

def unpublic (base : ExternalTypes) (F : Type) (x : @Public (types base F)) : @Public base := by
  cases x with
  | Transfer p l => exact @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer base p (unlate base F l)
  | Withdrawal p l => exact @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal base p (unlate base F l)

theorem late_roundtrip (b : ExternalTypes) (F : Type) (x : @Late b) :
    unlate b F (late b F x) = x := by cases x; rfl

theorem trace_roundtrip (b : ExternalTypes) (F : Type) (x : @Trace b) :
    untrace b F (trace b F x) = x := by cases x; rfl

theorem compilation_roundtrip (b : ExternalTypes) (F : Type) (x : @Compilation b) :
    uncompilation b F (compilation b F x) = x := by cases x; rfl

theorem link_roundtrip (b : ExternalTypes) (F : Type) (x : @CopyLink b) :
    unlink b F (link b F x) = x := by cases x; rfl

theorem times_roundtrip (b : ExternalTypes) (F : Type) (x : @Times b) :
    untimes b F (times b F x) = x := by cases x; rfl

theorem public_roundtrip (b : ExternalTypes) (F : Type) (x : @Public b) :
    unpublic b F (pub b F x) = x := by cases x <;> rfl

#print axioms late_roundtrip
#print axioms trace_roundtrip
#print axioms compilation_roundtrip
#print axioms link_roundtrip
#print axioms times_roundtrip
#print axioms public_roundtrip
end R1Z.PDict_FormatterTypeMaps
