# Selected Poseidon source completion

Status: deterministic mathematical/source-evaluator bridge complete on all
Boolean rows; literal Rust refinement and whole terminal composition remain
open.

The retained Lean chain proves the generic width-16 Poseidon algebra and
degree propagation, restricts the exact chronological source coordinate to
the Boolean trace table, classifies all eleven active pair rows, proves the
three inactive classes vanish, and packs four base coordinates in the exact
selected QM31 tower order.  The endpoint is
`sourcePoseidonLane_boolean`; it identifies the source polynomial callback
with the literal `packedPoseidon` residual on every table row.

No callback-success, valid-witness, or verifier-acceptance premise appears in
these identities.  The proof avoids substituting the old multilinear
extension off domain, an equality already known to be false.  It also does
not claim that the optimized mutable Rust loop implements the source
expression.

Focused checks used Lean 4.32.0 on the NUC through Tailscale under
`MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, and one Lean worker.
Promoted declarations report only `propext`, `Classical.choice`, and
`Quot.sound`.  Exact hashes and measurements are in
`results/v8-completion-fs-extraction-20260911/selected-poseidon-source-v1/report.json`.

The next deterministic gate is composition with the existing chronological
semantic and copy source lanes and then with the selected terminal.  This
milestone alone supplies no probability or global soundness claim.
