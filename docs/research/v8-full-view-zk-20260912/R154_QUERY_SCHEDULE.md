# R154: exact selected query schedule

The actual selected `query_schedule` is extracted from the retained callback
source and connected to the actual q22 and three-attempt nonzero sampler.
The sequence is FINAL256, nonce bytes 16..24 under GRIND_NONCE, q22,
PROFILE `AV8/query-batch/v1`, and rho.

The raw chronology theorem works for all prefixes and inputs and keeps outer
failure/divergence. Query failure returns callback Sampler with the query
sampler's advanced transcript. Rho failure returns callback Sampler with the
nonzero sampler's advanced transcript. A short nonce retains its slice panic.
The model theorem assumes only an explicit total byte oracle and that the
serialized final values fit usize. It proves the complete result and returned
Prefix, including the fields that this function carries unchanged.

This extraction's serializer uses wrapping arithmetic. R152 proves bounded
checked/wrapping equivalence, and R153 applies it to the symbolic iterator
invariant to prove the exact little-endian bytes. No concrete vector or large
recurrence is normalized. The external extraction templates are filled with
existing source implementations and explicit representation adapters; no axiom
is used to stand in for a source operation.

Seven changed production leaves compiled successfully. Exact commands, source
pins, unchanged raw generated output, adapters, complete audits and resource
evidence are retained in `evidence/r154-query-schedule`. The initial extraction
failed because the selected compile flags were omitted; those flags were
recovered from consistent pinned cached fingerprints and recorded. No resource
cap was raised. The disclosed cached `core.fmt.Formatter` type dependency remains.

The next proposition is actual `freeze`, then round-zero alpha and the ordered
shared-oracle call history. Full privacy and soundness remain open; no full
prefix correspondence is asserted. Verifier source and security settings are
unchanged, preserving the existing 999,790 / 999,532 CU evidence.
