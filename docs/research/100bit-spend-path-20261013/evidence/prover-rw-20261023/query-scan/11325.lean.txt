import R1Z.ProverRwQueryResult

/-! Focused final audit of the accepted query dependency chain only. -/
#print axioms R1Z.ProverRwQueryContains.loop_search
#print axioms R1Z.ProverRwQueryContains.contains_exact
#print axioms R1Z.ProverRwQueryMembership.search_success_iff
#print axioms R1Z.ProverRwQueryMembership.search_ne_false
#print axioms R1Z.ProverRwQueryMembership.contains_prefix_iff
#print axioms R1Z.ProverRwQueryScan.source_unfold
#print axioms R1Z.ProverRwQueryScan.dispatch_congr
#print axioms R1Z.ProverRwQueryScan.scan_finite
#print axioms R1Z.ProverRwQueryScan.queries_finite
#print axioms R1Z.ProverRwQueryTransition.mem_take_iff
#print axioms R1Z.ProverRwQueryTransition.mem_val_iff
#print axioms R1Z.ProverRwQueryTransition.contains_model
#print axioms R1Z.ProverRwQueryTransition.wrapping_succ
#print axioms R1Z.ProverRwQueryTransition.advance_q22
#print axioms R1Z.ProverRwQueryWord.dispatch_factored
#print axioms R1Z.ProverRwQueryWord.source_factored
#print axioms R1Z.ProverRwQueryWordTotal.offset_mul
#print axioms R1Z.ProverRwQueryWordTotal.offset_add
#print axioms R1Z.ProverRwQueryWordTotal.division_total
#print axioms R1Z.ProverRwQueryWordTotal.read_total
#print axioms R1Z.ProverRwQueryExecution.execute
#print axioms R1Z.ProverRwQueryExecution.queries_execute
#print axioms R1Z.ProverRwQueryModelChain.scan_cons_of_one
#print axioms R1Z.ProverRwQueryModelChain.chain_scan
#print axioms R1Z.ProverRwQueryModelChain.chain_draws
#print axioms R1Z.ProverRwQueryModelChain.scan_nodup
#print axioms R1Z.ProverRwQueryModelChain.queries_model
#print axioms R1Z.ProverRwQueryResult.finish_exact
#print axioms R1Z.ProverRwQueryResult.queries_characterization
