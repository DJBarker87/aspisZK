# Conditional transcript terminal checkpoint — 2026-10-15

`LiteralTerminalRunSpend.checked_witness_of_transcript_read_noHit` now compiles.
For an actual literal byte-protocol transcript of at least 33 rounds, it derives
a witness accepted by `SpendRelation.checkM31` from explicit reader/check
conditions and the absence of classifier hits. It reuses the committed
`LiteralTerminalSpend` extraction theorem and existing opening, pairing and
query-support results.

Compared with `LiteralTerminalSpend`, Good, AcceptedPairing and the matching
set cardinality are conclusions of supporting theorems instead of inputs to
this wrapper. The successful readers, coefficient checks, row-31/32 shapes,
validity, query decoding, first matches, residual batch equation and semantic
sumcheck equations remain explicit premises. Verifier acceptance is not yet
proved to supply those premises.

## Verification and reuse

Target: `LiteralTerminalRunSpend`; final attempt: `terminal-run-spend-d`.
Source base: `2ee03b0c53e673cf8adaecd5fb780cc81ea2aed6`.
Exit status: 0. Wall time: 94.889 seconds. Peak sampled process-group RSS:
3,592,032 KiB. Process swaps: 0. The single exported axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256:
`182e29e65f23bda9822022575fd42faa91dffbc5b00d1fe548728b9459baa104`.
Object SHA-256:
`e8a16221118980ed8c908dc76ec2e08811feb3b72d4d594d32e2d9036a9ce947`.

The first compile exposed stale helper objects built against the old protocol
signature. Their sources were unchanged, but their transitive dependencies
were incompatible. The existing checked protocol/run-facts/opening-good
objects in `lean-literal-byte-merge-20261015` were reused after source, object
and archive checks. An unnecessary helper rebuild was cancelled after those
objects were located; it is recorded as cancellation, not a mathematical
failure. A subsequent transcript-length simplification error was fixed by
using the existing round-length equality explicitly. No theorem premise was
weakened and no memory cap was raised.

The [evidence bundle](../evidence/lean-literal-terminal-run-spend-20261015/README.md)
retains the failed attempts, final success, old and current dependency pins,
and cancellation/cache-reuse evidence. The
[root artifact review](../evidence/j1-literal-terminal-run-spend-review-20261015.json)
checks those artifacts independently.

## Remaining boundary

The next conditional interface composes this theorem with generic FS2 D3;
it still requires an accepted execution to supply the explicit checks.
The current Rust semantic verifier is not covered by a retained complete
Rust-to-Lean translation: available extraction artifacts cover field parsers,
while the semantic loop and its arithmetic correspondence remain open.

This is not a final security result. Source/Pool and commitment correspondence,
sampler/query-budget correspondence, efficient extraction, full probability
composition, privacy and current runtime certification remain outstanding.
