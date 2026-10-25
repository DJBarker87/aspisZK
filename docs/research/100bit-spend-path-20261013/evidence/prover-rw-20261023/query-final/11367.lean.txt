import R1Z.ProverRwQueryRetry
-- One final focused axioms/interface audit; no frozen release replay.
#print axioms R1Z.ProverRwQueryAttempt.attempt_exact
#print axioms R1Z.ProverRwQueryBlock.model_window
#print axioms R1Z.ProverRwQueryBlock.block_source
#print axioms R1Z.ProverRwQueryCallerSplit.queries_factor
#print axioms R1Z.ProverRwQueryComplete.publish_finite
#print axioms R1Z.ProverRwQueryComplete.queries_policy
#print axioms R1Z.ProverRwQueryComplete.queries_complete
#print axioms R1Z.ProverRwQueryDecode.read_closed
#print axioms R1Z.ProverRwQueryFinishTransport.finish_transport
#print axioms R1Z.ProverRwQueryFinishTransport.query_transport
#print axioms R1Z.ProverRwQueryInstalled.query_exact
#print axioms R1Z.ProverRwQueryListStep.add_wrapping
#print axioms R1Z.ProverRwQueryListStep.body_advance
#print axioms R1Z.ProverRwQueryMaterial.materialize_bind
#print axioms R1Z.ProverRwQueryMaterialTransport.absorb_transport
#print axioms R1Z.ProverRwQueryMaterialTransport.materialize_transport
#print axioms R1Z.ProverRwQueryNativeAttempt.native_attempt_exact
#print axioms R1Z.ProverRwQueryOpening.opening_exact
#print axioms R1Z.ProverRwQueryPolicy.raw_transport
#print axioms R1Z.ProverRwQueryPolicy.policy_transport
#print axioms R1Z.ProverRwQueryPublish.branch_publish
#print axioms R1Z.ProverRwQueryRetry.attempt_transport
#print axioms R1Z.ProverRwQueryRetry.retry_transport
#print axioms R1Z.ProverRwQueryRetry.admitted_eight
#print axioms R1Z.ProverRwQuerySemantics.semantics_exact
#print axioms R1Z.ProverRwQuerySourceWindow.window_source
#print axioms R1Z.ProverRwQueryStop.run_finish
#print axioms R1Z.ProverRwQueryStop.run_at
#print axioms R1Z.ProverRwQueryTrace.loop_bind
#print axioms R1Z.ProverRwQueryTrace.loop_finite
#print axioms R1Z.ProverRwQueryTrace.trace_finite
#print axioms R1Z.ProverRwQueryWindow.list_window
#print axioms R1Z.ProverRwQueryWindow.window_total
#print axioms R1Z.ProverRwQueryWindowStop.stop_lt
#check @R1Z.ProverRwQueryComplete.queries_complete
#check @R1Z.ProverRwQueryPolicy.policy_transport
#check @R1Z.ProverRwQueryRetry.admitted_eight
