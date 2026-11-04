# Scanner call scope correction

Frozen revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer:780–807,
and NDT TX2:226 agree: this root calls the afterstate decoder, afterstate
encoder and Variant::S2.tag. Its standard/library boundary includes Box,
checked arithmetic and slice equality. It does not call hashv, SolanaDigest,
or a digest/error dictionary operation directly.

NEQ_HANDOFF's scanner next-deliverable text includes a runtime digest
slice/reply association. That is not a prerequisite at this root's direct
call sites. This correction does not certify any digest operation elsewhere
or change op43/op44 cohort authority. Any reached equality loop still needs
the ruling-B one-iteration native association and Lean induction; no whole
688-byte comparison is sent to Kani. No SHA implementation is modeled.

This is read-only source/inventory review, not a new native or composed pass.
