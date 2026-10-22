# S9 Rust range source-body finite correspondence

This packet proves a narrow finite value-level bridge. The natural-number model of the pinned Rust `Range::next` source body agrees with the existing Aeneas `StepUsize` iterator result, and the fixed S9 outer `0..2` states and callback `0..4` states have the listed old-value/next-value behavior. The successful source branch is justified under the `start < end` range bound, which ensures `start + 1` remains within the `usize` value bound.

The proof does not establish that the SBF compiler binary, MIR, or deployed runtime implements this source body. The pinned source comparison is documented in [source-comparison-reference.md](source-comparison-reference.md); its matching normalized method bodies are source evidence only. The SBF compiler build still reports an unknown commit hash, so no compiler-binary/source identity is claimed.

The exact Lean target, selected `LEAN_PATH`, direct import hash, source hash, object hash, launch receipt, memory metrics, and `#print axioms` reports are recorded under `S9RustRangeSourceBodyV3/evidence/`. The packet intentionally excludes compiled objects.
