import R1Z.PDict_Audit231
import R1Z.PDict_FileWorld244
import R1Z.PDict_CopyCorrect244
import R1Z.PDict_TapeCorrect244
import R1Z.PDict_OSRegression244
import R1Z.PDict_TapeSuffix244
import R1Z.PDict_RemainingDictionary231
import R1Z.PDict_OwnedSource244
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ArrayReference244
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Variant := PDict_OwnedSource244.aspis_r1_cost_probe.transport.Variant

def toReference : transport.Variant → Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def fromReference : Variant → transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

theorem from_to (variant : transport.Variant) : fromReference (toReference variant) = variant := by
  cases variant <;> rfl

theorem to_from (variant : Variant) : toReference (fromReference variant) = variant := by
  cases variant <;> rfl

abbrev native := PDict_RemainingDictionary231.native

/-- An installed OWNED REFERENCE, not a proof that shipped from_fn has been
replaced. Native equivalence must be checked for the actual monomorphic types;
the outstanding identity is recorded in the receipt rather than an axiom. -/
@[reducible] def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  { PDict_RemainingDictionary231.selected base ops with
    op255 := fun copy variant rows =>
      PDict_OwnedSource244.coefficients.owned copy (toReference variant) rows }

theorem op255_reference (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) {T : Type} (copy : core.marker.Copy T)
    (variant : transport.Variant) (rows : Array T 1024#usize) :
    (selected base ops).op255 copy variant rows =
      PDict_OwnedSource244.coefficients.owned copy (toReference variant) rows := rfl

theorem file_open_retained (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op14 (native base) (selected base ops) =
      @ExternalFuns.op14 (native base) (PDict_RemainingDictionary231.selected base ops) := rfl

theorem io_kind_retained (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op23 = (PDict_RemainingDictionary231.selected base ops).op23 := rfl

theorem entropy_retained (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    (selected base ops).op129 = (PDict_RemainingDictionary231.selected base ops).op129 := rfl

#print axioms from_to
#print axioms to_from
#print axioms op255_reference
#print axioms file_open_retained
#print axioms io_kind_retained
#print axioms entropy_retained
end R1Z.PDict_ArrayReference244

/- Final selected-closure axioms audit. The unused RowShape probe was checked
before the discriminant-name fix and is deliberately not imported into this
selected closure. No frozen-manifest or native adequacy claim follows. -/
#print axioms R1Z.PDict_TapeCore244.read_at
#print axioms R1Z.PDict_TapeCore244.read_success
#print axioms R1Z.PDict_TapeCore244.read_exhausted
#print axioms R1Z.PDict_TapeCore244.reads_inventory
#print axioms R1Z.PDict_TapeCore244.replay_inventory
#print axioms R1Z.PDict_TapeCore244.replay_reads
#print axioms R1Z.PDict_TapeCore244.reads_replay
#print axioms R1Z.PDict_TapeCore244.replay_append
#print axioms R1Z.PDict_TapeCore244.reads_compose
#print axioms R1Z.PDict_TapeCore244.replay_deterministic
#print axioms R1Z.PDict_EventWorld244.step_at
#print axioms R1Z.PDict_EventWorld244.exhausted
#print axioms R1Z.PDict_EventWorld244.mismatch
#print axioms R1Z.PDict_EventWorld244.success
#print axioms R1Z.PDict_EventWorld244.inventory
#print axioms R1Z.PDict_EventWorld244.law_at
#print axioms R1Z.PDict_EventWorld244.admission_frame
#print axioms R1Z.PDict_SinkCore244.options_frame
#print axioms R1Z.PDict_SinkCore244.sink_exact
#print axioms R1Z.PDict_SinkCore244.calls_exact
#print axioms R1Z.PDict_SinkCore244.emit_frame
#print axioms R1Z.PDict_SinkCore244.writes_inventory
#print axioms R1Z.PDict_SinkCore244.transport
#print axioms R1Z.PDict_EventWorld244.lookup
#print axioms R1Z.PDict_EventWorld244.to_tape
#print axioms R1Z.PDict_EventWorld244.replay_inventory
#print axioms R1Z.PDict_EventWorld244.replay_append
#print axioms R1Z.PDict_EventWorld244.replay_laws
#print axioms R1Z.PDict_OSRegression244.first_error
#print axioms R1Z.PDict_OSRegression244.second_success
#print axioms R1Z.PDict_OSRegression244.error_success_replay
#print axioms R1Z.PDict_OSRegression244.no_fixed_outcomes
#print axioms R1Z.PDict_TapeCore244.read_suffix
#print axioms R1Z.PDict_TapeCore244.replay_suffix
#print axioms R1Z.PDict_TapeCore244.reads_suffix
#print axioms R1Z.PDict_EventWorld244.replay_suffix
#print axioms R1Z.PDict_World244.fileDecidableEq
#print axioms R1Z.PDict_World244.entropy_signature
#print axioms R1Z.PDict_World244.step_at
#print axioms R1Z.PDict_World244.exhausted
#print axioms R1Z.PDict_FormatterQuotient244.type3
#print axioms R1Z.PDict_FormatterQuotient244.type27
#print axioms R1Z.PDict_FormatterQuotient244.op23
#print axioms R1Z.PDict_FormatterQuotient244.op85
#print axioms R1Z.PDict_FormatterQuotient244.debug_calls
#print axioms R1Z.PDict_FileWorld244.flush_source
#print axioms R1Z.PDict_FileWorld244.kind_source
#print axioms PDict_CopySource244.coefficients.copy_owned_loop.body
#print axioms PDict_CopySource244.coefficients.copy_owned_loop
#print axioms PDict_CopySource244.coefficients.copy_owned
#print axioms PDict_TapeSource244.world.Reply.Insts.CoreCloneClone.clone
#print axioms PDict_TapeSource244.world.Tape.Insts.CoreCloneClone.clone
#print axioms PDict_TapeSource244.world.next
#print axioms PDict_TapeSource244.world.retry_collision
#print axioms R1Z.PDict_Advance244.value
#print axioms R1Z.PDict_CopyCell244.cell
#print axioms R1Z.PDict_CopyCell244.done_cell
#print axioms R1Z.PDict_CopyCorrect244.loop_value
#print axioms R1Z.PDict_CopyCorrect244.owned_value
#print axioms R1Z.PDict_TapeView244.lookup
#print axioms R1Z.PDict_TapeView244.capacity
#print axioms R1Z.PDict_TapeView244.advance
#print axioms R1Z.PDict_TapeView244.source_index
#print axioms R1Z.PDict_TapeCells244.exhausted
#print axioms R1Z.PDict_TapeCells244.matched
#print axioms R1Z.PDict_TapeCells244.mismatched
#print axioms R1Z.PDict_TapeCorrect244.reference_next
#print axioms R1Z.PDict_RowBounds244.append_bound
#print axioms R1Z.PDict_RowChunk244_0.part_0_length
#print axioms R1Z.PDict_RowChunk244_0.part_0_bound
#print axioms R1Z.PDict_RowChunk244_0.part_1_length
#print axioms R1Z.PDict_RowChunk244_0.part_1_bound
#print axioms R1Z.PDict_RowChunk244_0.part_2_length
#print axioms R1Z.PDict_RowChunk244_0.part_2_bound
#print axioms R1Z.PDict_RowChunk244_0.part_3_length
#print axioms R1Z.PDict_RowChunk244_0.part_3_bound
#print axioms R1Z.PDict_RowChunk244_0.part_4_length
#print axioms R1Z.PDict_RowChunk244_0.part_4_bound
#print axioms R1Z.PDict_RowChunk244_0.part_5_length
#print axioms R1Z.PDict_RowChunk244_0.part_5_bound
#print axioms R1Z.PDict_RowChunk244_0.part_6_length
#print axioms R1Z.PDict_RowChunk244_0.part_6_bound
#print axioms R1Z.PDict_RowChunk244_0.part_7_length
#print axioms R1Z.PDict_RowChunk244_0.part_7_bound
#print axioms R1Z.PDict_RowChunk244_0.length
#print axioms R1Z.PDict_RowChunk244_0.bound
#print axioms R1Z.PDict_RowChunk244_1.part_0_length
#print axioms R1Z.PDict_RowChunk244_1.part_0_bound
#print axioms R1Z.PDict_RowChunk244_1.part_1_length
#print axioms R1Z.PDict_RowChunk244_1.part_1_bound
#print axioms R1Z.PDict_RowChunk244_1.part_2_length
#print axioms R1Z.PDict_RowChunk244_1.part_2_bound
#print axioms R1Z.PDict_RowChunk244_1.part_3_length
#print axioms R1Z.PDict_RowChunk244_1.part_3_bound
#print axioms R1Z.PDict_RowChunk244_1.part_4_length
#print axioms R1Z.PDict_RowChunk244_1.part_4_bound
#print axioms R1Z.PDict_RowChunk244_1.part_5_length
#print axioms R1Z.PDict_RowChunk244_1.part_5_bound
#print axioms R1Z.PDict_RowChunk244_1.part_6_length
#print axioms R1Z.PDict_RowChunk244_1.part_6_bound
#print axioms R1Z.PDict_RowChunk244_1.part_7_length
#print axioms R1Z.PDict_RowChunk244_1.part_7_bound
#print axioms R1Z.PDict_RowChunk244_1.length
#print axioms R1Z.PDict_RowChunk244_1.bound
#print axioms R1Z.PDict_RowChunk244_2.part_0_length
#print axioms R1Z.PDict_RowChunk244_2.part_0_bound
#print axioms R1Z.PDict_RowChunk244_2.part_1_length
#print axioms R1Z.PDict_RowChunk244_2.part_1_bound
#print axioms R1Z.PDict_RowChunk244_2.part_2_length
#print axioms R1Z.PDict_RowChunk244_2.part_2_bound
#print axioms R1Z.PDict_RowChunk244_2.part_3_length
#print axioms R1Z.PDict_RowChunk244_2.part_3_bound
#print axioms R1Z.PDict_RowChunk244_2.part_4_length
#print axioms R1Z.PDict_RowChunk244_2.part_4_bound
#print axioms R1Z.PDict_RowChunk244_2.part_5_length
#print axioms R1Z.PDict_RowChunk244_2.part_5_bound
#print axioms R1Z.PDict_RowChunk244_2.part_6_length
#print axioms R1Z.PDict_RowChunk244_2.part_6_bound
#print axioms R1Z.PDict_RowChunk244_2.part_7_length
#print axioms R1Z.PDict_RowChunk244_2.part_7_bound
#print axioms R1Z.PDict_RowChunk244_2.length
#print axioms R1Z.PDict_RowChunk244_2.bound
#print axioms R1Z.PDict_RowChunk244_3.part_0_length
#print axioms R1Z.PDict_RowChunk244_3.part_0_bound
#print axioms R1Z.PDict_RowChunk244_3.part_1_length
#print axioms R1Z.PDict_RowChunk244_3.part_1_bound
#print axioms R1Z.PDict_RowChunk244_3.part_2_length
#print axioms R1Z.PDict_RowChunk244_3.part_2_bound
#print axioms R1Z.PDict_RowChunk244_3.part_3_length
#print axioms R1Z.PDict_RowChunk244_3.part_3_bound
#print axioms R1Z.PDict_RowChunk244_3.part_4_length
#print axioms R1Z.PDict_RowChunk244_3.part_4_bound
#print axioms R1Z.PDict_RowChunk244_3.part_5_length
#print axioms R1Z.PDict_RowChunk244_3.part_5_bound
#print axioms R1Z.PDict_RowChunk244_3.part_6_length
#print axioms R1Z.PDict_RowChunk244_3.part_6_bound
#print axioms R1Z.PDict_RowChunk244_3.part_7_length
#print axioms R1Z.PDict_RowChunk244_3.part_7_bound
#print axioms R1Z.PDict_RowChunk244_3.length
#print axioms R1Z.PDict_RowChunk244_3.bound
#print axioms R1Z.PDict_RowChunk244_4.part_0_length
#print axioms R1Z.PDict_RowChunk244_4.part_0_bound
#print axioms R1Z.PDict_RowChunk244_4.part_1_length
#print axioms R1Z.PDict_RowChunk244_4.part_1_bound
#print axioms R1Z.PDict_RowChunk244_4.part_2_length
#print axioms R1Z.PDict_RowChunk244_4.part_2_bound
#print axioms R1Z.PDict_RowChunk244_4.part_3_length
#print axioms R1Z.PDict_RowChunk244_4.part_3_bound
#print axioms R1Z.PDict_RowChunk244_4.part_4_length
#print axioms R1Z.PDict_RowChunk244_4.part_4_bound
#print axioms R1Z.PDict_RowChunk244_4.part_5_length
#print axioms R1Z.PDict_RowChunk244_4.part_5_bound
#print axioms R1Z.PDict_RowChunk244_4.part_6_length
#print axioms R1Z.PDict_RowChunk244_4.part_6_bound
#print axioms R1Z.PDict_RowChunk244_4.part_7_length
#print axioms R1Z.PDict_RowChunk244_4.part_7_bound
#print axioms R1Z.PDict_RowChunk244_4.length
#print axioms R1Z.PDict_RowChunk244_4.bound
#print axioms R1Z.PDict_RowChunk244_5.part_0_length
#print axioms R1Z.PDict_RowChunk244_5.part_0_bound
#print axioms R1Z.PDict_RowChunk244_5.part_1_length
#print axioms R1Z.PDict_RowChunk244_5.part_1_bound
#print axioms R1Z.PDict_RowChunk244_5.part_2_length
#print axioms R1Z.PDict_RowChunk244_5.part_2_bound
#print axioms R1Z.PDict_RowChunk244_5.part_3_length
#print axioms R1Z.PDict_RowChunk244_5.part_3_bound
#print axioms R1Z.PDict_RowChunk244_5.part_4_length
#print axioms R1Z.PDict_RowChunk244_5.part_4_bound
#print axioms R1Z.PDict_RowChunk244_5.part_5_length
#print axioms R1Z.PDict_RowChunk244_5.part_5_bound
#print axioms R1Z.PDict_RowChunk244_5.part_6_length
#print axioms R1Z.PDict_RowChunk244_5.part_6_bound
#print axioms R1Z.PDict_RowChunk244_5.part_7_length
#print axioms R1Z.PDict_RowChunk244_5.part_7_bound
#print axioms R1Z.PDict_RowChunk244_5.length
#print axioms R1Z.PDict_RowChunk244_5.bound
#print axioms R1Z.PDict_RowChunk244_6.part_0_length
#print axioms R1Z.PDict_RowChunk244_6.part_0_bound
#print axioms R1Z.PDict_RowChunk244_6.part_1_length
#print axioms R1Z.PDict_RowChunk244_6.part_1_bound
#print axioms R1Z.PDict_RowChunk244_6.part_2_length
#print axioms R1Z.PDict_RowChunk244_6.part_2_bound
#print axioms R1Z.PDict_RowChunk244_6.part_3_length
#print axioms R1Z.PDict_RowChunk244_6.part_3_bound
#print axioms R1Z.PDict_RowChunk244_6.part_4_length
#print axioms R1Z.PDict_RowChunk244_6.part_4_bound
#print axioms R1Z.PDict_RowChunk244_6.part_5_length
#print axioms R1Z.PDict_RowChunk244_6.part_5_bound
#print axioms R1Z.PDict_RowChunk244_6.part_6_length
#print axioms R1Z.PDict_RowChunk244_6.part_6_bound
#print axioms R1Z.PDict_RowChunk244_6.part_7_length
#print axioms R1Z.PDict_RowChunk244_6.part_7_bound
#print axioms R1Z.PDict_RowChunk244_6.length
#print axioms R1Z.PDict_RowChunk244_6.bound
#print axioms R1Z.PDict_RowChunk244_7.part_0_length
#print axioms R1Z.PDict_RowChunk244_7.part_0_bound
#print axioms R1Z.PDict_RowChunk244_7.part_1_length
#print axioms R1Z.PDict_RowChunk244_7.part_1_bound
#print axioms R1Z.PDict_RowChunk244_7.part_2_length
#print axioms R1Z.PDict_RowChunk244_7.part_2_bound
#print axioms R1Z.PDict_RowChunk244_7.part_3_length
#print axioms R1Z.PDict_RowChunk244_7.part_3_bound
#print axioms R1Z.PDict_RowChunk244_7.part_4_length
#print axioms R1Z.PDict_RowChunk244_7.part_4_bound
#print axioms R1Z.PDict_RowChunk244_7.part_5_length
#print axioms R1Z.PDict_RowChunk244_7.part_5_bound
#print axioms R1Z.PDict_RowChunk244_7.part_6_length
#print axioms R1Z.PDict_RowChunk244_7.part_6_bound
#print axioms R1Z.PDict_RowChunk244_7.part_7_length
#print axioms R1Z.PDict_RowChunk244_7.part_7_bound
#print axioms R1Z.PDict_RowChunk244_7.length
#print axioms R1Z.PDict_RowChunk244_7.bound
#print axioms R1Z.PDict_RowTable244.length
#print axioms R1Z.PDict_RowTable244.bounds
#print axioms R1Z.PDict_RowTable244.table_val
#print axioms R1Z.PDict_RowTable244.index_bound
#print axioms PDict_OwnedSource244.row.ORDER
#print axioms PDict_OwnedSource244.row.row
#print axioms PDict_OwnedSource244.coefficients.owned_loop.body
#print axioms PDict_OwnedSource244.coefficients.owned_loop
#print axioms PDict_OwnedSource244.coefficients.owned
#print axioms PDict_OwnedSource244.coefficients.copy_owned_loop.body
#print axioms PDict_OwnedSource244.coefficients.copy_owned_loop
#print axioms PDict_OwnedSource244.coefficients.copy_owned
#print axioms PDict_OwnedSource244.world.Reply.Insts.CoreCloneClone.clone
#print axioms PDict_OwnedSource244.world.Tape.Insts.CoreCloneClone.clone
#print axioms PDict_OwnedSource244.world.next
#print axioms PDict_OwnedSource244.world.retry_collision
#print R1Z.ProverCommitDeployedFuel22.RustProverRefinement
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
