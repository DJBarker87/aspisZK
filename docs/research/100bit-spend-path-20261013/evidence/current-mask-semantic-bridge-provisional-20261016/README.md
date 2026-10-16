# Generic mask bridge: provisional evidence

The target `ExtractedMaskSemanticBridge` passed Lean 4.32 in attempt f, with
one standard-only axiom report. Its historical dependency evidence is not yet
complete; this bundle is not final source or release admission.

`proofs.tar.gz` retains the exact successful source and object, attempts a–f,
the additional `ExactTowerFinite` attempt, runner versions, import pins and
environment snapshots. Its embedded `SHA256SUMS` indexes 65 files. The outer
manifest repeats the original remote manifest unchanged. `root-review.json`
records the theorem and runner review; `independent-audit.json` records the
independent archive/source/receipt checks. The outer `SHA256SUMS` pins this
published bundle.

Successful target: 3.23 s, 4,063,528 KiB peak RSS, zero process swaps, exit 0.
The cgroup cap was 4 GiB high / 6 GiB maximum / zero swap. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.

The theorem requires canonical source inputs and an explicit field map with
basis compatibility. It derives actual extracted-call success and the mapped
mask formula. It does not derive those input conditions from verifier
acceptance, instantiate the concrete wide field, or prove the full spend.

See the [design and precise evidence limits](../../design/J1-CURRENT-MASK-SEMANTIC-BRIDGE-20261016.md).
