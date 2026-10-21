# Recorded log accounting preflight

The actual recorded definition runs the compiled prover once and the literal
verifier once. `RawCutProverCompiler.compiled_experiment_eval` gives the original
experiment log followed by a repeat of its verifier log. Its proof uses
`OracleProgramRecording.eval_record`, proved by induction over Program; the
pure metadata construction returns `.done` and adds no reads.

The composition law is `RawCutProverCompiler.experiment_eval`. The verifier query
bound is `R19BudgetOriginalReads.verifier_queries`, not its distinct-read
corollary. The bound uses induction over lists (`flatten_length_le`) and the
sampler/program induction `R19BudgetSamplerReads.query_tail_length`.

Hence the chronological list is `(prover ++ verifier) ++ verifier`, giving
Q + 2*561 = Q+1122 <= Q+1161, without acceptance or BoundaryEvidence. No
compiler replay of the prover occurs. No concrete oracle/program evaluation
is needed. The next consumer is HeadlineV2.final_soundness and its direct
cost corollary; their numeric parameters remain unchanged.
