# R130: raw independent law and fixed-tape mean boundary

Source base: `56d4a311483bb3bb88780e13e4b9e8969b8516b7`.

Three focused leaves are confirmed compiled: `CirclePairRawIndependentLaw`,
`IndependentMeanFixedTape`, and `SamplerProgramQueryBound`.

The confirmed boundary covers the raw OOD-pair independent law and fixed-tape
independent mean, and a conservative all-branches trace bound of 66. It makes
no `FreshFrom`, source-callback, or source-distribution claim.

Privacy and soundness remain open.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r130_evidence.py
```
