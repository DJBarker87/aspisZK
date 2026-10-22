# Row 31 literal query-run witness

`AspisR1.LiteralQuerySampleRunWitness.valid_row31_success_decodes_with_run` strengthens the retained row-31 sampler-validity result. For a successful literal payload sample, it returns both the strict `LiteralQueryRead.decode` result as `Fin 22` coordinates and the exact `QueryFirstRead.result` list run whose first component is `.ok xs`. The helper fixes the erased prefix, row-31 absorb, byte-addressed oracle, and query-sampler initial state used by the original proof.

The challenge value here is `List Nat`; it is not a serialized U32LE byte array. This theorem is sampler-model evidence only. It does not establish source/caller refinement or production standard-library lowering.

The inspected concrete schedule theorem `Query31ConcreteMaterializedScheduleFull.successful_default_concrete_materialized_query_schedule` retains the absorbed transcript state, eight materialized digest pairs, and a Q22 scan chain for `actualQueryWords`. The prepared-query legality theorem then converts the successful schedule's U32 output to an ordered legal `Fin 22` enumeration. Neither theorem links that output list to `row31PayloadQueryRun`: the missing join is equality of the absorbed initial state and the eight actual query-state block/advance inputs used by the literal sampler with the corresponding materialized digest-pair arrays. No such source/transcript bridge was found in the inspected owners. The production `Transcript::queries` caller and standard-library lowering therefore remain open.

The focused Lean 4.32 compile exited 0 in 3.91 seconds, with 3,067,379,712 bytes peak process RSS and zero swaps. `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`. The exact selected import profile and command are retained in `receipt/`.
