# Independent source and evidence review

Reviewed 2026-10-15 without rebuilding Lean.

The target repository source, final snapshot, attempt snapshot, and receipt agree at SHA-256 `0890f2243440fbe87b617091e2fa016853bb3c68f5802e78e43490e11cc05279`. The three repository source paths and snapshots validate, as do the receipt, compiled-object archive member hashes/sizes, and the existing `SHA256SUMS`. The attempt exited 0 in 1.50 s with 3,582,868 KiB peak RSS and zero swap. Five public reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The checked prefix thresholds are exact: `gamma_at_prefix` requires `27 < rs.length`, `kappa_at_prefix` requires `28 < rs.length`, `first_at_prefix` requires `29 < rs.length`, and `second_at_prefix` requires `30 < rs.length`. Given a successful complete `SelectedOpeningRead.read (rs ++ tail) = some p`, `stages_of_full` identifies staged reads at rows 25–27, 25–28, 25–29, and 25–30 with projections of `p`. The prefix lemmas combine that implication with each stage's append-stability theorem.

The staged readers themselves are prefix-only: `readGamma` reads 25–27, `readKappa` adds 28, `readFirst` adds 29, and `readSecond` adds 30. None computes an earlier-stage value using a later field. The result is one-way from successful full read to matching stage projections; it is not an iff saying the full read succeeds exactly when a stage succeeds. These are typed-list facts and do not prove source execution, challenge correspondence, or acceptance.

The import snapshot paths were corrected to their actual `import-sources/R1*.lean` filenames; repository `source_path` values were already correct. `SHA256SUMS` was refreshed after this metadata fix and the review note.
