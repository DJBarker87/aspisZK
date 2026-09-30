# R131: fixed-tape QM31 and operational cursor bounds

Source base: `61b446d5b0f7adc30d313b375aee2b2e48040216`.

Two focused R19 leaves are confirmed compiled: `IndependentMeanFixedTapeQM31`
and `SamplerCursorTightBound`.

The first is a structural fixed-tape certificate for the source-shaped QM31
challenge.  The second proves that the operational `challengeRun` has an
actual trace bound of `8` queries.  The fixed-tape certificate remains the
conservative bound `66`, because it counts the source-program branches and
retains the rollover/read ghosts.

This boundary makes no `FreshFrom`, source-callback, source-distribution,
privacy, or soundness claim.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r131_evidence.py
```
