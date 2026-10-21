# S3 `Weights::pair` v23 typed-operations extraction candidate

This packet records a successful nonempty Charon/Aeneas extraction of the normalized `Weights::pair` candidate using the real `EbyKDot` carrier layout. It is source-cut feasibility evidence only. It contains no Lean objects or binaries.

The extraction emitted the whole candidate `pair_root` body and the expected helper bodies; all three EbyK methods are marked opaque by Aeneas. The Rust shim methods behind those declarations are unreachable placeholders, so their generated `fail panic` meanings are rejected for proof use.

`typed-ops/sources/AspisR1WeightsPairCutEbyKDotOpsV1.lean` maps the generated candidate carrier to the separately retained actual EbyK carrier and exposes typed `new`, `push`, and `finish` operation slots. This adapter’s local compile evidence lacks a full launch receipt and is therefore not counted as a release-grade compile. The separately green mini-clone compile is retained under `diagnostics/` only and does not establish generated-owner coherence. No concrete Ops implementation is supplied yet.

The packet pins frozen baseline bytes, candidate source, LLBC, translation manifest, commands, receipts, resource caps, and declaration inventory. `span-audit.json` recomputes the actual `Weights::pair` spans from the retained files using balanced braces. The earlier `source-pins.json` offsets do not identify those spans and remain historical metadata only; the addendum and its diff are authoritative. `python3 check_packet.py` validates hashes, successful extraction receipts, declaration presence, and the expected opaque EbyK method entries.

Open work and the exact `FrozenWeightsPairSemantics = CandidatePairSemantics` equality frontier are listed in `normalization-frontier.json`; the event-order rows map each change to frozen/candidate line spans and name the required Result/state equality. No whole-caller source refinement is claimed.
