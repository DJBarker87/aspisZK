# Exact remaining op223/V240 obstruction

No stable PV_CB_Op223Source.op223_source exists. No shipped-source canonical
counterexample was found. The target is not established.

1. Native route:actual no-stub compress_tagged_tuple vs owned/reference. Two
   original full16 gates (canonical tag/data/lambda and raw inputs) each retried
   once at900s, unwind18, taskset0–3, unchanged6G/8G/swap0/Tasks64; both exit124,
   wall15:00.00. Four new full16 canonical output-lane partitions, same unwind18,
   timeout180, all exit124, wall3:00.00. A timeout is no verification verdict.
   Exact per-run inputs/commands/metrics are in RESUME5-KANI-TABLE.md and each
   named receipt; wrapper GNU RSS and sampled cgroup peak are separate.
2. Direct route:the cfg(aeneas_ref) by-value array shim is an extraction-only
   wrapper whose body is one call to actual shipped compress_tagged_tuple.
   Transparent extraction imports the body but Aeneas exits2 with:

   `ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation`

   Optimized opaque-wrapper extraction exits0 but compressor remains opaque;
   no template axiom is installed and no source law is inferred. Additional
   optimized/MIR/force-inlining configurations did not expose a validated
   transparent compressor body. All source/config/error snapshots remain.
3. Producer route:actual legacy/forest tuple_cells extract and their offsets,
   row/bank metadata and bounded totality are proved. Actual16 returned words
   are canonical under selected trace-cell read validity; tag/sampler input
   invariants are checked. Sampled complete-Result caller transport is proved
   under explicit canonical16 native agreement. That agreement and compiled
   trace selected-read validity are not supplied. Auxiliary row translation
   Charon exits0; Aeneas exits2 with the same escaping-reference diagnostic.
   Whole registry coverage is not claimed.

Smallest proposition sufficient for the unchanged V164 consumer:

`ops.op223 = @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)`

Its pointwise form quantifies over every tag/slice/lambda in the function type.
A bounded canonical16 agreement does not imply this unrestricted equality via
funext. The independent callback model obstruction is not a shipped-source
counterexample. No read-only ProverRw consumer was weakened or edited.

Before/after:V164 P_source_p6, P_proof_bytes and reservation unchanged. Both
consumer source files are byte-identical to revision237e13556180d2ce0320a2760f89b35b5f4f02bb.
Rows23/73; endpoint premise removals0. New helper conditions are local theorem
hypotheses, not new endpoint premises. Fallback native op117/circle/pole gates
continue under the authorized12-run budget; the live tally is authoritative.
