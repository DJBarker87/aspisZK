# Stage 3 preflight

Seven concrete preimages were reconstructed from the exact Lean fixture seeds,
program IDs, and expected account keys. Python hashlib agrees with all seven
expected keys (diagnostic computation, not a Lean digest proof). Input lengths
and padded-block counts are recorded in JHs_CALLS.json. Each SHA block is at
most 64 round transitions, materialized separately; no whole SHA reduction is
planned. The existing JGz_SHAU00 checked-block proof shape is reused.

The next consumer is JHs_FixtureCertificates: named per-call digest equations,
off-curve predicates, and model-success proofs. Runtime op38 installation and
decoder/authentication composition remain outside these mathematical equations.

The input proofs encountered opaque extracted constants and a simplifier loop
in U64 byte conversion. Those are proof failures, not digest counterexamples.
The replacement unfolds the conversion definitions once in sequence and uses
the fixed array length property. No recursion/heartbeat limit is increased.
