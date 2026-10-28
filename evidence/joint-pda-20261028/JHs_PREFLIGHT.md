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
The final replacement proves a standalone eight-byte serialization equality
using the existing decoded-value theorem and uses the fixed array length property. No recursion/heartbeat limit is increased.

Final generator specialization: entry's 173-byte input uses a named split into
two 64-byte prefixes and a 45-byte tail; cons_append simplification proves that
split, and length_append proves its length. All other raw lengths are small.
All padding proofs name rawLength before reducing the small padding expression;
all complete digests use JGz_HashTools.hash_chunks plus checked block theorems.
The initial direct-padding and direct-entry-length depth failures are retained
in attempts 013, 019 and 020. No unchanged failed job was rerun.
