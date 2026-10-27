# Reviewed stop of the field projection

The changed field projection was stopped by TERM to its own timeout process after 725.28 seconds. Its wrapper completed and recorded exit -15, peak aggregate RSS 4,896,067,584 bytes, swap0; the scope is inactive. No assertion result or counterexample is inferred. No cap was raised.

Reason: source inspection localized the extraction guard to generated FnOnce adapters and generic drop glue. Test a semantic extraction alternative that handles those drops precisely rather than continuing a costly duplicated 21-step hash recurrence. Charon provides `--precise-drops --desugar-drops --monomorphize`: explicit destructor calls are retained and monomorphized, rather than erased. This is an existing extractor option, not an extractor patch or a Drop-as-no-op override. If it fails, retain its exact error and continue the P6/Lean work.
