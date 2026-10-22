# Same-witness row-31 scan output consumer

`row31_source_trace_output` consumes (1) the same source `materializedOutputs` witness for the digest pairs and returned block/advance arrays, (2) the literal sampler's `pairsRun = .ok xs` result over those source-derived pair functions, and (3) the exact materialized `scanOut` result for those same arrays. The pair-function list views are derived internally from `materializedOutputs` using `S4PairFunctionViewsV1`; `pairsRun_scanOut` then proves the returned U32 values equal the literal list `xs`.

The premise obtaining `hpairs` remains the existing row-31 prefix/digest composition, and `htrace` remains the actual scanner endpoint supplied by the concrete DriverTrace bridge. The theorem does not assert either missing upstream fact. Lean 4.32 focused compile, selected profile, resource logs, and standard-axiom report are in `receipt/`. The packet contains no compiled objects.
