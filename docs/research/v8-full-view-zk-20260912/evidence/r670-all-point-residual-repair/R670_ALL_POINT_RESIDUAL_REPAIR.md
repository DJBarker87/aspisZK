# R670 all-point residual repair

Status: focused-green release candidate. Root review and promotion are pending;
this packaging step did not stage, commit, push, or replay any target.

R669 establishes conditional exact repair for an arbitrary pair of ordinary
and structured seven-coefficient targets. R670 derives the formerly missing
point-zero equation rather than assuming it: the ordinary target 0-plus-4
boundary and nonzero quarter and kappa force the point-zero functional through
the full original source weights, including tau image updates. The resulting
repair reaches both target polynomials, preserves all three point functionals,
271 sparse coordinates, 22-by-4 modeled query roots, 32 first folds, and
inactive balance.

The statement remains conditional on both target alpha evaluations, both
0-plus-4 boundaries, nonzero quarter/kappa, and the exact residual determinant.
It does not derive targets from legal same-public witnesses or native source
execution; it does not establish the H1 active-row condition, actual root or
determinant law, shared oracle, complete published-view simulator, privacy,
soundness, or end-to-end security.

R669 final run `1791115140213164000`: revision
`93623cf50cc47bc4696b0521494170c02d0db1a9`, source SHA-256
`4963a30f704a5eccbb27fd54c6580fb4859154e4974f0a90e8568b493e4638a6`, exit 0,
wall 1.83 seconds, RSS 3,322,828 KiB, swap 0. Its one axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound`.

R670 final run `1791115400083154000`: revision
`3462e3d1547577b97ecf2c30e624344aa169ac07`, source SHA-256
`63a4099022b73e80258451c32cbe7bc3d9e9692afdaafd9e6babf8e8c54fbc1c`, exit 0,
wall 1.41 seconds, RSS 3,302,368 KiB, swap 0. All three reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

R669's compile used the R666 cache before R666 promotion. The retained source
and R666 focused receipt pin that dependency to SHA-256
`d4f29e5d11d79533505d1c9769ea171236feddcabab3082bb6eeaee2b178e0dd`.
