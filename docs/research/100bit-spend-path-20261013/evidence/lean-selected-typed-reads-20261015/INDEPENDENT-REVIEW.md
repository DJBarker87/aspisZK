# Independent evidence review

Reviewed 2026-10-15 by a second agent, without rebuilding Lean.

The current repository source `lean/SelectedTypedReads.lean`, the final snapshot, and the attempt receipt agree at SHA-256 `6536c236e8842e265d0442b8ae3d9aacedd4c9cec204ca035ca59e0a0a17a5f4`. All six direct-import repository paths and snapshots in the manifest were checked for existence and matching hashes. The compiled-object archive entries match the listed hashes and sizes, and the attempt log has six public reports, each listing only `propext`, `Classical.choice`, and `Quot.sound`. The recorded attempt exited 0 in 1.48 s with 3,581,000 KiB peak RSS and zero swap.

The source proves three conditional representation equalities from `RawRoundDecode.decode ... = some rs`, by applying `SelectedRawCanonical.encode_of_decode`: semantic, opening, and transcript readers over the encoded typed records agree with the corresponding raw readers. It also proves append stability at the explicit thresholds `24 < rs.length`, `31 < rs.length`, and `32 < rs.length`, respectively. Those bounds preserve the selected index ranges; the results do not claim source execution or acceptance correspondence.

The manifest's five import snapshot names were corrected to the actual `import-sources/R1*.lean` filenames. Repository source paths remain the actual unprefixed Lean filenames. `SHA256SUMS` was regenerated after that metadata correction and this review note.
