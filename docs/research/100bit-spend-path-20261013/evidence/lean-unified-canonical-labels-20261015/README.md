# Unified sampler canonical-label theorem

`R1UnifiedCanonicalLabels.samp_allLabels` proves that every address asked by the current 33-row `UnifiedSampler`, in every continuation and for every row/message input (including the totalized invalid-message branches), satisfies `CanonicalByteAddress.Canonical`. The proof reuses the canonical `Addr.ofBytes` constructors for absorb, squeeze, advance, initialization, reseed, and the query chain.

The three preserved attempts were compiled at base revision `3c79ec30fa44f408c716bb345050c137e907fa67`, with swap disabled and a 4G/6G cgroup. Attempts a and b failed with local elaboration errors and emitted `sorryAx` reports; they are retained as failures. Attempt c is green and its single public theorem report depends only on `propext` and `Quot.sound`. All exact snapshots, receipts, logs, direct import source/object pins, and deterministic object archives are listed in `source-manifest.json`.

This theorem covers the sampler program only. It does not prove that a full adversarial program has no additional byte-string queries, establish an adversary decoder/restriction theorem, or transfer a shared-oracle security law.
