import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeFailures35
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

/-- No source failure or divergence is made into an inner wire error. -/
theorem failed_read (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : i<count) (err : Aeneas.Std.Error)
    (he : Slice.index_usize e i = .fail err) :
    @host_sumcheck.merge_evaluations_loop _ (ProverRwDictionaryTower.selected ops)
      e a (array p) count i = .fail err := by
  unfold host_sumcheck.merge_evaluations_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [host_sumcheck.merge_evaluations_loop.body,hi,if_true,he,bind_tc_fail]

theorem divergent_read (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : i<count) (he : Slice.index_usize e i = .div) :
    @host_sumcheck.merge_evaluations_loop _ (ProverRwDictionaryTower.selected ops)
      e a (array p) count i = .div := by
  unfold host_sumcheck.merge_evaluations_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [host_sumcheck.merge_evaluations_loop.body,hi,if_true,he,bind_tc_div]

theorem wire_error (ops : ExternalFuns)
    (e : Slice (core.result.Result Q r1_wire.Error)) (a count i : Usize)
    (p : Nat → Q) (hi : i<count) (err : r1_wire.Error)
    (he : Slice.index_usize e i = .ok (.Err err)) :
    @host_sumcheck.merge_evaluations_loop _ (ProverRwDictionaryTower.selected ops)
      e a (array p) count i = .ok (array p,some (.Err err)) := by
  unfold host_sumcheck.merge_evaluations_loop
  rw [ProverRw19LoopBind.loop_bind]
  simp only [PV_RunJoin_MergeStep35.error ops e a count i p hi err he,bind_tc_ok]

#print axioms failed_read
#print axioms divergent_read
#print axioms wire_error
end R1Z.PV_RunJoin_MergeFailures35
