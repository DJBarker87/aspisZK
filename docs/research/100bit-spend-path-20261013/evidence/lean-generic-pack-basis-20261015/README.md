# Generic PackBasis constructor evidence

This bundle preserves the focused `R1GenericPackBasis` run. Attempt `a` failed in proof plumbing: its rewrite tried to replace a variable in a goal already expressed using the embedding witnesses. Attempt `b` uses the equality witnesses directly and compiled successfully.

The final declaration `AspisR1.GenericPackBasis.ofEmbedding` constructs `R0P.PackBasis e.fieldRange` from an explicit four-coordinate independence hypothesis over the source field. Its axiom report is `[propext, Classical.choice, Quot.sound]`. This is a generic constructor only; it does not prove the concrete M31-to-WideExact independence premise or relate the Lean packing map to Rust.

Source revision: `f1edebd66d8ea21178b8f4f34b4c623fc3934413`. Final source SHA-256: `431009e0f198e37ffbcc1ecc2e2962ccf230a81de5b63864c2909053c1624f67`. The successful receipt records exit 0, 1.36 s wall time, 3,302,116 KiB peak RSS, zero swap, and cgroup limits of 4 GiB high / 6 GiB max / 0 swap.

Both attempts retain their exact source snapshots, receipts, compiler logs, time logs, and source hash sidecars. The imported `R0P.CoreExt` and transitive `R0P.Core` source snapshots match repository files by hash; their cached objects were symlinked from the pinned `aspis-fs-generic-20261006` workspace. The runner and environment files are preserved under `runner/`.
