# Focused local check: scalar-dot chunk iterator

**Checked locally; NUC replay pending.** The maintained `PoseidonM31DotChunkIterator` component reuses the actual Aeneas standard-library step-by-four iterator specifications. It proves initialization, advancement with saturation at the end, and stopping. In the seven-input caller the last chunk therefore ends at seven. The full scalar-dot and internal-pair caller theorems remain pending; this component does not establish the requested end-to-end security result.

The focused macOS Lean 4.32.0 check exited 0 in 341.44 seconds, with peak RSS 1,884,438,528 bytes and zero reported swaps. All three `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Cold loading of the prebuilt import closure dominated wall time; no dependency build or whole-package regression was run.

`receipt.json` pins the exact source, compiled object, direct import source/object, compiler commit, Mathlib commit, base source revision, and command/import path. The source was compiled under the frozen filename `PoseidonM31DotChunkIterator-v2.lean` with output module path `PoseidonM31DotChunkIterator.olean`; the maintained source is byte-identical. No binary objects are added to Git.

`cache-coherence/` confirms the direct RangeIter object matches the current pinned NUC workspace and all 219 shared Aeneas subtree objects match byte for byte. These are read-only object comparisons, not a replay.

The NUC was not admitted for this check because its live workload reservations exceeded the configured safe aggregate budget. No other workload or container configuration was changed. This receipt is local focused evidence, not a NUC release-manifest result. Production Rust and runtime artifacts are unchanged.
