# S9 candidate body prefix and terms producers (source-only)

This packet freezes two independently compiled producer lemmas for the selected candidate helper body. `S9CandidateBodyPrefixV1` extracts the same-call powers and scalar-factor results from the actual generated body prefix. `S9CandidateBodyTermsV1` depends on that exact prefix object and extracts the four ordered term-call witnesses while retaining the exact post-terms residual.

The launch revisions differ and are preserved independently in each receipt. The object files are pinned by path and SHA but are not included. Each target includes its full captured `LEAN_PATH`, command, closure report, raw Lean log, timing, and concurrency evidence.

This does not establish Rust standard-library `from_fn` correspondence, full candidate helper closure, or global S9 closure. Run `python3 check_packet.py` to verify sources, receipts, object metadata, closure/import pins, named axiom reports, and source-only packaging.
