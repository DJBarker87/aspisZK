# R406 sampler word distribution evidence

This package preserves the three focused attempts and the exact source/runner used for the final green target. The promoted research source is byte-identical to the successful captured input.

The final theorem concerns the source word extraction as a finite bijection. A uniform 32-byte `State` maps bijectively to eight 32-bit words; splitting each word into its high 14-bit and low 18-bit coordinates is another bijection. Therefore the eight masked 18-bit candidates are jointly uniform. This does not establish an independent-answer law for the memoized shared oracle, a challenge/kernel/retry law, or a security bound.

The final compile used the pinned R126 Lean 4.32 cache under a 5 GiB high / 7 GiB maximum / zero swap / 128-task scope with `-j1 -M4500`. The successful run was 1.56 seconds, 3,232,976 KiB GNU-time child peak RSS, zero swap, exit 0. All four complete `#print axioms` reports use only `propext`, `Classical.choice`, and `Quot.sound`. Two earlier failed source revisions are retained verbatim and visibly include `sorryAx`; they are not release evidence for the final theorem.

`dependency-cache-identities.json` records read-only SHA-256 identities for the two direct local import oleans and pinned Mathlib Fin/BigOperators sources and cached artifacts. `verify_evidence.py` is read-only and emits its audit to stdout.
