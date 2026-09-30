# R135: explicit selected-schedule execution

Source base: `bd75cc78edda899373aedfbe6fcd204c2e17cad9`.

`SelectedResearchScheduleExecution` compiles under the recorded 5G/7G,
zero-swap runner.  It defines a pure execution view by composing the existing
absorb, QM31 challenge, circle-pair, nonzero and q22 run functions.  The run is
not an alias for `eval`; `eval_run` proves equality by the existing exact
component execution theorems, preserving all typed outcomes and returned
states through rho.

The selected measured verifier source remains unchanged.  Its frozen R117
`relation_callback.rs` hash is
`4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f`,
and the measured 999790 / 999532 CU endpoint is not reinterpreted as a
universal resource bound.

The first remaining proposition is the exact source-to-run correspondence for
that frozen callback, including the source error translation and the
unreachable-domain argument between kappa and the ordinary absorbs.  No
source distribution, privacy or soundness result is claimed.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r135_evidence.py
```
