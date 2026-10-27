import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.ProverRw21RecursiveDefinitions
open ProverRwFull
-- Inspect fixed-point construction rather than unroll concrete recurrences.
#print host_semantic.d_tail_sum
#print host_sumcheck.prove_sumcheck_rounds
#check host_semantic.d_tail_sum.eq_def
#check host_sumcheck.prove_sumcheck_rounds.eq_def
end R1Z.ProverRw21RecursiveDefinitions
