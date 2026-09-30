# R126: sampler representation and typed callback prefix

Source base: `3c06a11a80d253506aaadb00f810943f69eb525b`.

The focused NUC replay compiled two R19 plumbing leaves under Lean 4.32.0:
`SamplerRawStateRepresentation` identifies one 32-byte squeeze block with
eight little-endian 32-bit words, and `RelationPrefixProgram` gives the typed
relation-callback prefix through the final256/grind-nonce boundary while
leaving wrapper programs explicit.

## Exact proved boundary

- `stateRawEquiv_word` and `stateRawEquiv_word_offsets` prove the pure byte/
  word representation transport.
- `uniform_state_words` transports a finite mean across that representation;
  it does not assert oracle freshness or a sampler law.
- `relationPrefixProgram` is a typed program skeleton for the selected
  callback prefix, including explicit wrapper parameters and visible program
  results.

The two leaves had exit 0, zero swap, and four axiom audits. Dependency pins
are the 272-entry R122 overlay at
`evidence/r122-adaptive-first-read/dependency-pins.json`.

The initial missing-overlay formulation and the K1 import-only route were not
proved. K1 imports hit Lean's `-M4500` interpreter memory guard even at the
import baseline; those attempts are recorded as OPEN in the evidence.

## Explicitly open

This evidence does not prove the source sampler distribution, callback/shared-
oracle correspondence, freshness, privacy, or soundness. The next boundary is
to connect the typed prefix and pure word representation to the actual bounded
sampler and its visible failure/cache behavior.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r126_evidence.py
```
