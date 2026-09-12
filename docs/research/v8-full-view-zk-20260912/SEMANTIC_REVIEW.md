# Independent semantic review

Date: 2026-09-12. Scope: read-only adversarial review of this milestone by a
separate agent; not an independent human cryptographic audit.

## Findings accepted

1. The narrow status labels are conservative: no valid-payment distinguisher,
   source instance, efficient simulator, hybrid bound or global epsilon is
   claimed.
2. The Rust harness calls the actual crate-private encoder/layout APIs but
   manually applies the reconstructed repair and balancing rule. It proves a
   nonzero annihilator for the 88-coordinate column-3 fixed schedule, not the
   rank-56 calculation or a full generated-source/full-proof result. The
   README and status were narrowed accordingly.
3. Three generated-build preimages remain unavailable and profile/release
   hashes bind identifiers, not executable semantics. P0 remains partial.
4. The intended deployed experiment must use the proof-account public key as
   the nonce and `generate_for_mask_nonce()`, not ambiguously select the
   independent-nonce `generate()` API. The experiment and manifest were
   corrected.
5. The no-rank-gate conclusion is supported for the reconstructed host
   performance path only, not every future production q22 adapter.
6. The Lean results are honest generic lemmas/definitions. Their premises do
   not construct V8 source instances. The computational target still lacks a
   security-parameter-indexed adversary machine and randomized-test model.

## Residual premise graph

Before a global endpoint, the work still needs same-public valid-witness
classification; source-derived joint conditional kernels; seed/PRG and shared
ROM laws with adaptive query/conflict bounds; root/salt-consistent chronological
simulation; a q22 bad-schedule bound or separately reviewed publication gate;
abort/retry/session accounting; a full generated-source and honest-prover
adapter; an efficient witness-free simulator; and explicit global composition.
