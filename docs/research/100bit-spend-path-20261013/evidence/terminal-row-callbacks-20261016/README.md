# Terminal row-callback and conversion evidence

This checkpoint contains two complete focused evidence bundles and an
independent root review. The seven successful sources are maintained in
`../../lean/`; their bytes match the archived successful snapshots. See
[the scope and result table](../../design/J1-TERMINAL-ROW-CALLBACKS-20261016.md).

The callback archive retains 23 attempts: five successful targets and
18 failures. The extension archive retains two successful targets. Fifteen
successful axiom reports contain only standard Lean axioms. The generated
extension slice emits zero reports and is counted only as a compile.

Each archive preserves exact sources, receipts, raw Lean and timing logs,
direct-import pins, resource reservations, environment and runner pins,
and successful compiled outputs. `archives.json` pins the compressed bytes.
`root-review.json` records the independent source/output/log review;
`audit-bundles.py` reproduces it after unpacking the two archives into their
named directories under `/private/tmp`. It checks represented dependency
edges only; missing older objects are covered by the referenced predecessor
evidence rather than claimed to be in these archives.

The final all-row wrapper derives successful reads from fixed dimensions and
`limb.val < 4`. The extension word theorem derives its reads from its fixed
four-word input type. Neither assumes those successful reads as an additional
public premise. Neither proves the surrounding `from_fn`, full matrix layer,
terminal caller, or accepted-verifier/security theorem.

Root also checked the three copied extension declaration blocks against the
pinned generated G source spans. The exact generated file is retained in
the preceding terminal translation archive. The recorded workspace base
revision is preserved as recorded; new proof snapshots have independent
hashes and are published on top of `b40ad6372`.

No production Rust or measured runtime artifact is changed here.
