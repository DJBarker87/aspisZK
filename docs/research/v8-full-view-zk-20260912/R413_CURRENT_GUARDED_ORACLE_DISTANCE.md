# R413 guarded oracle distance

The promoted theorem bounds the difference between lazy memoized-oracle and independent-answer means for any causal program and any `[0,1]` observer by a guardFresh indicator mean. Cached reads are not resampled, and `FreshFrom` is not assumed. The guard is only a comparison experiment.

No source-specific numeric guard-hit probability, freshness theorem, or security claim is established. The next obligation is to bound guard-hit probability over the actual initial state, adversary cache, retries, and full callback.

See [R413GuardedOracleDistance.lean](lean/AspisV8R19/R413GuardedOracleDistance.lean) and [saved evidence](evidence/r413-guarded-oracle-distance/README.md).
