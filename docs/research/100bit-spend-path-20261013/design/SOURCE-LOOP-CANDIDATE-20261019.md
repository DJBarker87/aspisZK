# Isolated source candidate for complete proof extraction

This branch replaces iterator-dependent semantic boundary/Horner loops and the batched flush/map constructs with explicit indexed operations. Their isolated Charon/Aeneas jobs now emit full definitions, without the former external templates. Body refinement proofs are in progress; this is not yet a proved source migration.

The decoder adopts exactly the existing V10 indexed-loop candidate, SHA256 47562d76a47ba602aacbbdd61c9b97c4429ba9700aa96e8ea49d3c4ccab9b444. Its successful-output canonicality and byte-readback proofs already exist in the actual-decode-k-loop-canonicality and actual-decode-k-byte-readback packets. Caller/input bounds, no-panic behavior and release source adoption still require their explicit obligations.

Production research retains the measured sub-1.2M implementation. Do not merge this candidate before focused source proofs, byte/hash/checkpoint equivalence, native verifier checks and the changed-artifact runtime/CU gates. The 313-CU smallest measured stage-1 headroom means loop spelling cannot be assumed free. No full soundness/privacy or release claim is made here.
