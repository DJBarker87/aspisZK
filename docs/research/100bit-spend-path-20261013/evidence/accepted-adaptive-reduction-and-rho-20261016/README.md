# Acceptance-scoped adaptive reduction and actual final-row recovery

`AcceptedAdaptiveFiatShamir` reuses the existing first-bad-event reduction with decoder completion required only on accepting executions. This permits validity and strict-format facts to come from source verifier acceptance. The event, terminal D3 premise and symbolic query-dependent bound are unchanged. `AcceptedAdaptiveMembershipSoundness` transports the result to absence of a spend-relation witness, with the specification-level choice extractor; efficient knowledge extraction is separate.

`RawPublicRhoRecovery` derives final-row public recovery from the actual chronological semantic, opening and query trace. The fixed row-32 expression is kept opaque where necessary, and explicit frame equalities avoid recursive normalization. `FullPublicRhoCasePublicAPI` supplies the actual bounded prover-experiment case, including public rewrite lemmas for its trace/chain wrappers and a convenience theorem without an extra table premise. The earlier private-wrapper attempt is superseded and is not a maintained joint-import target.

Combined with the previous early/opening cases, each of the 33 public-selection cases is checked. Their total composition, raw-byte adaptive compiled injection and conditional bound are being verified next. Source acceptance-to-formatting, terminal source correspondence, efficient extraction and full privacy/runtime closure remain open. No complete 100-bit claim follows from this checkpoint.

Focused Lean 4.32.0 NUC checks; all exits 0, process swaps 0, and printed axioms standard only. Per-target receipts retain source/import pins, cap, wall time, RSS and axiom outputs.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `AcceptedAdaptiveFiatShamir` | 1.228 | 1824616 | 2 |
| `AcceptedAdaptiveMembershipSoundness` | 0.868 | 1809856 | 2 |
| `RawPublicRhoRecovery` | 1.828 | 3569688 | 1 |
| `FullPublicRhoCasePublicAPI` | 1.744 | 3554840 | 3 |
