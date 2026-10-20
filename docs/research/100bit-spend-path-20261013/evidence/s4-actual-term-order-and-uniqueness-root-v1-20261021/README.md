# Actual term order and unique input products

`actual_trace_term_indices` proves that the source contribution list visits exactly List.range' start (end-start), in order. It derives terminal range exhaustion from the successful actual source body. No independent start/stop or contribution-index premise is supplied.

`term_bytes_trace_unique` proves that checked offset/slice/copy execution yields one byte array for a fixed source buffer, slot and term. `matched_term_product_unique` then uses the same parser/read/conversion calls to show one product value for each fixed source input and term, independent of which successful trace exposes it.

Focused checks passed4.049s/2.536s, process RSS2,257,043,456B/2,251,292,672B, zero swaps. All three axiom reports are standard-only. One rejected no-goals diagnostic is retained. Semantic polynomial identification, outer seven-batch accumulation, P6 RustStd and frozen caller/runtime remain open. No production source changed.
