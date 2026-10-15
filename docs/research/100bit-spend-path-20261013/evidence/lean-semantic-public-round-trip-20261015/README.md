# Semantic public wire round-trip Lean evidence

This bundle records six focused attempts for `R1SemanticPublicWireRoundTrip`: attempts a–e failed during proof plumbing and are retained; attempt f is green. The final source and object hashes match the f receipt. Receipt metrics, runner/environment pins, direct-import pins, logs, exact snapshots and sidecars are recorded in `source-manifest.json`.

Attempt f reports three `#print axioms` results, all using `[propext, Classical.choice, Quot.sound]`. All attempts ran under the recorded 4G/6G/0-swap cgroup caps. The source base is `136b746805f3438507732622c9b4e50f36bf49f9`.

The result proves round-trip and length properties for the Lean semantic-public wire model under its stated canonical option-shape premise. It does not establish Rust parser refinement, account or transaction binding, or a runtime security result.
