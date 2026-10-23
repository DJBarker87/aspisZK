# Part 53: migrated terminal closure and source Poseidon contract

**Target not yet established.** Branch `codex/cx-prover-commit53-20261023`.
Proof allocation J10500–J10599; dependency builds use BUILD-53 labels.
No shipped crate/program source is changed.

## Stage 1: migrated terminal closure

BUILD-53-1 checks the three part-52 roots against the D178 object overlay,
its pinned retained dependencies, then the D175 joint cache. All three roots
already have migrated objects; zero missing modules. The capped pass exits 0
in 0.03 s, peak RSS 17424 KiB, zero swaps. Source revision
`3bf0a58481bc98110878803c3d8aacfec2371375`. No unchanged dependency is recompiled.
This reuses the D178 rebuild rather than repeating it. Exact targets, environment,
source pins and limits are in `evidence/prover-commit53-20261023/build/` in the
100bit-spend-path tree. Shared sources and objects are not overwritten.

J10500 imports the full three-root union and prints all three top theorem
axiom reports. It exits 0; each report uses exactly
`[propext, Classical.choice, Quot.sound]`. Its full GNU-time receipt is retained
in `lean/time-10500.log`, alongside source SHA, revision and output in
`lean/J10500.json`. This is an import/axioms audit, not payload equality.

## Endpoint before/after

Complete verbatim endpoint modules are retained in `endpoint/before.lean.txt`
and `endpoint/after.lean.txt` with pins. They are unchanged. The deployed
`RustProverRefinement` premise, quantifiers, failure events and bound remain
explicit and unchanged. No FSExperiments join or release claim is made.
