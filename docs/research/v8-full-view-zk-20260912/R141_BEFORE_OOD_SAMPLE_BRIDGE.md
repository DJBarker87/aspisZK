# R141: exact selected-callback sampler helper

Source base: `e21d26a1f17312db5a8f7dc54a495d80ce95b36d`.

R141 closes the deterministic value/error/state correspondence for both
branches of the `sample` helper extracted from the selected R136 callback.
It proves that:

- `sample(t, false)` is the already-proved exact R137 QM31 sampler, with a
  successful value converted into the R136 field type;
- `sample(t, true)` is the already-proved exact three-attempt nonzero sampler;
- source challenge exhaustion is mapped to callback `Error.Sampler`; and
- every branch retains the exact advanced transcript state.

The focused NUC leaf compiled under the 5/7 GiB cgroup in 1.85 seconds, with
3,704,028 KiB peak process RSS and zero swap.  `map_err_mapChallenge` uses no
axioms; the two sampler theorems use only `propext`, `Classical.choice`,
`Quot.sound`, and the already-extracted `core.fmt.Formatter` axiom.

The first remaining proposition for the exact `before_ood` body is the
generated `bytes` serializer: its loop must be related to the concatenation
of 16-byte little-endian encodings for the first 358 QM31 values.  The full
callback chronology, R137 q22 source binding, oracle admissibility, privacy,
and soundness remain open.  No verifier source or CU endpoint changed; the
selected verifier remains **999,790 / 999,532 CU**.

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r141_evidence.py
```
