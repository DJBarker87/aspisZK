# S4 query-values caller with ClaimPowers coordinate bounds

This consumer replaces the 29 pointwise coordinate-bound assumptions with a canonical ClaimPowers input and the explicit array carrier identity `prefixArrayToCurrent gPrefix = claimArrayToFast claimPowers`. It reuses the green opaque four-callback field-result consumer, so the callback result existentials remain intact and linked to the same `gPrefix` passed through `query_values`.

The exact array identity is still a caller premise. The Rust `array::from_fn` model boundary, ClaimPowers caller provenance in the verifier, and accepted-run/headline theorem remain separate. The accepted coordinate bridge object was absent from the local warm cache; a single focused source rebuild produced the exact owner-pinned object hash, with no dependency rebuild.
