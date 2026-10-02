# R278/R279 saved publication evidence audit

read-only saved evidence audit; no Lean reruns, source edits, or proof/security conclusions

Audit result: **PASS**.

| Target | Source/copy | Checksums | Metrics | Axioms | Runner/revision |
|---|---:|---:|---:|---:|---:|
| R278 | pass | pass | pass | 3 / pass | pass |
| R279 | pass | pass | pass | 3 / pass | pass |

The R278 raw adapter has three root declaration blocks byte-equal to the generated R276 declarations and nine independently recomputed transitive helper body comparisons. The only replacements permitted by this audit are `core.num.U32.` → `Std.U32.` twice for R249 B.sub and `31#i32` → `31#u32` once for the R156 M31.mul shift count. R276 and R156 M31 layouts match (`Std.U32`); R249 B is `Std.U32`; the R278 file declares no B or M31 type shadow.

Both saved compile logs report exit status 0, zero swaps, pinned Lean 4.32.0, revision `e8601f2d13149484f3a6a0304cd48892821363c4`, resource caps 5G/7G/0 swap/128 tasks, and flags `-j1 -M4500`. All six axiom reports match the saved manifests and `axioms.txt` and use only `propext`, `Classical.choice`, and `Quot.sound`.

This is a saved artifact and metadata audit. No Lean rerun or source-semantics/security conclusion was made.
