# Candidate full-query field evidence

`CandidateQueryFieldEvidence` is a reusable proposition for one reached candidate query. It explicitly retains that the selected candidate dots callback returned `candidateValues`, and that the Current-carrier values map back to that exact returned array. It also carries the reached query index/opening, exact source opening slice, scanned 608-byte prefix, canonical output coordinates, and four literal field-result facts over `claimArrayToFast claimPowers`.

`candidate_query_success_field_evidence` derives this proposition from the same successful complete candidate `queryWithOps`. It derives the reached index bound and strict-scan proof length from existing small prefix facts, obtains the exact 832-byte query slice from the emitted opening reader theorem, then applies the callback-output result to the callback array obtained from the source-shaped query prefix.

The theorem retains strict scan success, gamma/ClaimPowers evidence, and the caller array identity `fullArrayToCurrent g = claimArrayToFast claimPowers`. The packet does not claim to close the separate Rust Std/runtime extraction boundary.

This source-only packet contains no compiled `.olean`. Direct producer sources and selected object hashes are recorded in `receipts/direct-import-pins.json`.
