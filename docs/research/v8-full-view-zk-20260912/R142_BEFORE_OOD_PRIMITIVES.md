# R142: exact callback transcript primitives

Source base: `eca829ea45d44c85597c8d876d352ec5ffa346b4`.

R142 closes the deterministic R136 callback bridge for transcript creation
and absorption.  The generic absorb theorem covers both the source's packed
path and its long-message path and identifies the exact duplex frame, decoded
label, payload bytes, hash call, and next transcript state.

The focused NUC leaf compiled under the 5/7 GiB cgroup in 1.75 seconds, with
3,689,000 KiB peak process RSS and zero swap.  Both printed theorems use only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is present.

Together with R141, all transcript operations called directly by the
extracted `before_ood` body are now source-bound.  The first remaining
proposition is the callback's generated QM31-vector serializer, after which
the complete pre-OOD chronology can be composed.  The later R137 q22 source
bridge, oracle admissibility, privacy, and soundness remain open.  No verifier
source or CU endpoint changed; the selected verifier remains **999,790 /
999,532 CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r142_evidence.py
```
