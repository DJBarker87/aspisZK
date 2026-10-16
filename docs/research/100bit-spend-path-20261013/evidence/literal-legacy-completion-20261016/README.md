# All 33 legacy decoder cases on the literal raw-byte run

`LiteralLegacyDecoderCompletion.decodes_and_follows` proves successful decoder reconstruction of every actual round, using `UnifiedTotalCase.decodes_and_follows`. The actual raw-byte verifier trace, after an arbitrary consistent raw prover prefix, projects exactly to the older verifier trace. The old query bound and both collision exclusions follow from the one raw 11-target event. No bound on adversarial input length is introduced.

This closes the erased-transcript decoder completion bridge. The background sampler still uses the legacy canonical address carrier; its raw-address transport and literal committed-word enrichment are the next bridges. This is not yet a complete Fiat–Shamir soundness theorem or a deployed Rust refinement.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `RawBoundedCollision` | 0.928 | 1815728 | 6 |
| `RawBoundedProgram` | 0.943 | 1818320 | 5 |
| `LiteralLegacyRun` | 2.857 | 3640480 | 4 |
| `LiteralLegacyVerifierTrace` | 1.591 | 3625908 | 4 |
| `LiteralLegacyDecoderCompletion` | 1.712 | 3645744 | 1 |
