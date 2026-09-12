# Replayable source run to sampled relation data

`SameBodyReplayableRunFromSampledIntegration.successful_replayable_run_classifies_sampled_relation`
starts from one successful execution of the existing replayable source script.
It uses that execution's actual source/OOD/gamma, middle and later boundaries,
then executes `buildFromSampled` on the same body and records.  The result is
either a `Ready` value with exact `fromSampled` provenance and `Data.Checked`,
or a named parser, inverse, opening-pipeline or increment rejection.

This closes the deterministic source-prefix composition for this slice.  It
does not prove that the complete selected verifier accepts only the successful
constructor branch, derive the functional producer from pinned Rust, identify
the supplied hash view with the chronological final oracle, or provide a
random-oracle probability law.

Focused NUC compile used pinned Lean 4.32 and the private union cache.  It
exited 0 in 3.04 seconds wall time with 6,747,276 KiB peak RSS and zero swap.
Source SHA-256 was
`7b4eaec827f325a56ef3c14e529ff5f43a998e866e843afc49572b05f4149e21`;
OLean SHA-256 was
`34a580be51e8bfe8bf6903db94b320da28d53bd75c57b4b9c35a976397a3fcd8`.
The endpoint reports only `propext`, `Classical.choice` and `Quot.sound`.
Dependencies were cache-reused, not rebuilt.
