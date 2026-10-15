# Semantic public wire Lean evidence

This focused bundle preserves four finished Lean targets and all seven receipt-backed attempts: `R1PublicIndexListCodec` (attempts a/b), `R1SemanticPublicWire` (a/b), `R1SemanticPublicWireInjective` (a), and `R1SemanticPublicWireSound` (a/b). Three proof-plumbing attempts failed and are retained; the four final attempts exit successfully. Exact source hashes, source revision, receipt metrics, imports, cached objects, and runner pins are recorded in `source-manifest.json`.

The final `#print axioms` outputs are recorded in the successful attempt logs and summarized in the manifest. The final targets use only the standard axioms listed there. Failed drafts are preserved as attempt artifacts and are not final sources. Runner receipts report explicit 4G/6G/0-swap cgroup limits.

The wire module is a Lean representation of the modeled fields, index codec, and variant option shape. Injectivity is about the modeled carrier-to-public projection; `encode_of_decode` is a reverse-codec fact for the mathematical list model. These results do not establish Rust parser refinement, account or transaction binding, or a runtime security result. `SemanticPublicWireRoundTrip` remains outside the targets claimed here.

`R0P.Core` was imported through a symlink in the focused NUC workspace. Its source is pinned from the local historical tree and the resolved cached object bytes are retained here; the manifest does not claim that this local source snapshot was copied from the focused workspace.
