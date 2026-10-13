# Focused sampler and D18 Lean evidence checkpoint

`manifest.json` inventories 14 successful focused targets, their exact local source hashes, NUC receipts and sidecars, output/timing logs, imported-source hashes, compiled-object hashes, and complete `#print axioms` results. `validate_manifest.py` checks these links, exit status, the 4G/6G/zero-swap caps, wall time/RSS/swap, import edges, all source `#print axioms` commands and output declarations, and rejects any `sorryAx` or nonstandard axiom. Accepted axiom names are `propext`, `Classical.choice`, and `Quot.sound`.

The sampler entries cover `R1SamplerCarry`, `R1SamplerDigits`, `R1SamplerPass`, `R1SamplerLongDivision`, `R1SamplerMachineBounds`, `R1SamplerAddDigits`, `R1SamplerArithmetic`, `R1SamplerAddBridge`, `R1SamplerRanking`, and `R1SamplerNatModel`. The D18 entries cover `R1D18Transport`, `R1D18PointWeights`, and `R1D18RawPoint`. `R1DualPadQuadratic` is listed separately as an algebraic pad component, with `R1DualPad` as its dependency. These formal results are limited to their Lean statements; this evidence inventory does not establish Rust source correspondence, probability accounting, protocol security, privacy closure, or a release decision.

The manifest distinguishes evidence capture worktree HEAD from per-source task-start revisions. Provenance records `3638d7546f6e03a1afb0eaabdb1cff38d1631e84` for SamplerCarry, SamplerLongDivision, D18Transport, and D18PointWeights. The other ten target files use `a7ff42dc8068119ba1aea4e7bda471a01177b5be`; root confirmed that commit as their task-start/source base. Every exact source hash is also checked against the successful compile receipt and sidecar.

The compiled objects are preserved in `compiled-objects.tar.gz`; its deterministic members are listed in the manifest with hashes. To restore loose objects after checkout, run from this checkpoint directory:

```sh
tar -xzf compiled-objects.tar.gz
```

The validator checks the archived object hashes directly and also checks any restored loose copies. Run it from the repository root:

```sh
python3 docs/research/100bit-spend-path-20261013/evidence/lean-sampler-transport-chain-20261013/validate_manifest.py
```

`R1D18OpeningWeights` remains excluded from the green set. Its latest recorded attempt b exited nonzero; the owner reported an unavailable `R0C.SemStatement` object and an import-threshold failure. Its pending source snapshot is retained separately and is not treated as compiled evidence.
