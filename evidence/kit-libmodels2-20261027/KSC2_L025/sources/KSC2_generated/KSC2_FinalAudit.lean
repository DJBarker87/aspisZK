import KSC2_BackCorrection
import KSC2_P7Pins

/- A focused co-import and full audit of the new top roots; no release premise is removed. -/
#print axioms KSC2.range_collect
#print axioms KSC2.range_rev
#print axioms KSC2.range_enumerate
#print axioms KSC2.range_step_by
#print axioms KSC2.iter_collect
#print axioms KSC2.iter_rev
#print axioms KSC2.iter_enumerate
#print axioms KSC2.iter_step_by
#print axioms KSC2.option_ok_or
#print axioms KSC2.unwrap_or_else
#print axioms KSC2.map_lazy
#print axioms KSC2.windows_zero
#print axioms KSC2.windows_positive
#print axioms KSC2.window_contents
#print axioms KSC2.windows_next_some
#print axioms KSC2.windows_next_none
#print axioms KSC2.shared_back_some
#print axioms KSC2.shared_back_none
#print axioms KSC2.mutable_back_repeats_consumed
#print axioms KSC2.exhausted_has_no_remaining
#print axioms KSC2.mutable_any_loses_writeback
#print axioms KSC2.mutable_all_loses_writeback
#print axioms KSC2.mutable_back_disagrees_with_empty_spec
#print axioms KSC2.fold_step0
#print axioms KSC2.fold_step1
#print axioms KSC2.fold_step2
#print axioms KSC2.fold_loop
#print axioms KSC2.fold_body_eq
#print axioms KSC2.fold_factor
#print axioms KSC2.mutable_fold_result
#print axioms KSC2.mutable_fold_loses_writeback
#print axioms KSC2.mutable_enumerate_forward
#print axioms KSC2.mutable_enumerate_restore
#print axioms KSC2.mutable_rev_forward
#print axioms KSC2.mutable_rev_restore
#print axioms KSC2.mutable_step_zero
#print axioms KSC2.mutable_step_positive
#print axioms KSC2.front_reaches_exhausted
#print axioms KSC2.guarded_back_exhausted
#print axioms KSC2.guarded_singleton
#print axioms KSC2.active_back_writeback
