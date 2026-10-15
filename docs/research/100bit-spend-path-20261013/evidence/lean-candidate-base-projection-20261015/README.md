# Candidate base projection focused proof

Target `R1CandidateBaseProjection` was compiled in the pinned NUC workspace with the 4 GiB high / 6 GiB max / 0 swap / 128 task cap. Attempts a–d failed at candidate-membership theorem elaboration due to recursion-depth limits; all exact source snapshots, sidecars, receipts, logs, and timing records are retained. Attempt e succeeded with maxRecDepth 4096 and an opaque candidate-family boundary plus a generic uniform-lane helper.

The checked module derives base-field typing of `rowsOf rowEquiv t` from typed recovered words and `t ∈ ConcreteBinding.candidates (...)`. It also proves that coordinate projection followed by embedding recovers each such cell. Axiom audits for all three public theorems are `[propext, Classical.choice, Quot.sound]`. This does not connect parsed source bytes to candidate membership or prove preservation of the spend relation under M31-to-Wide mapping.

Source revision: `c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`. Final source SHA-256: `cdae8d0b2c495e17aba07ba2815c9eeb14599466cce586eb06656ea5c7cf9a37`. Final object SHA-256: `a09cddac4b74b2c3c6e5a017dd79e29366cbc5eee90c37ee5cd8054dbee6b288`.
