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

## Stage 2: retained source Poseidon callable

The additional leading/full-pair dependency preflight schedules 55 retained
modules. BUILD-53-2 builds six, then exposes Lean's namespace-directory
resolution at module 7: `AspisR1.PoseidonGroupSliceModel` exists in D178's
cache but is hidden by the new private `AspisR1` directory. This is a missing
artifact in the selected search directory, not a theorem failure. The exact
failed output and source/dependency hashes are retained.

The D178 read-only link completion pattern repairs the environment. It links
14696 existing cache objects and excludes all 55 planned compile outputs; no
shared object is overwritten. BUILD-53-3 then builds the remaining 49 modules
successfully, sequentially under 6G/8G/zero-swap/64 limits, with aggregate RSS
and ten-minute no-progress stops. Every printed accepted axiom report is
standard. Exact per-module targets, revision, hashes, dependency fingerprints,
exit, wall, RSS, swaps and full axiom reports are in
`poseidon-build/modules-audited.json` and the accompanying raw logs.

J10502 proves `AspisR1.PoseidonCallable53.source_success`: from the actual
boxed point and canonical z/successor/xor12 arrays, the retained source cut
succeeds canonically and returns all four packed scalar residuals. No leading,
full or internal branch success/model image is assumed. J10503 proves
`AspisR1.CompositionCallable53.run_success`, discharging the previously explicit
Poseidon callable contract from the retained composition continue branch.
The original public transcript preparation input remains.

J10501 is a rejected alias-elaboration draft (implicit array size); J10502
adds that size binder without changing the intended proposition or limits.
J10502: exit 0, wall 1.89 s, peak RSS 4147548 KiB, zero swaps. J10503: exit 0,
wall 1.69 s, peak RSS 4202536 KiB, zero swaps. Both top theorems print exactly
`[propext, Classical.choice, Quot.sound]`; full source snapshots and receipts
are in `lean/J1050{1,2,3}.*`. Source revision is the stage-1 commit plus
the exact compiled source hashes in the receipts.

These are retained source-cut results. The wrapper's extraction-candidate
Rust and the frozen native Rust have different low-fold and array-construction
syntax, and the leading external layer is factored differently. Native
correspondence, guards, terminal model identification and complete payload
equality are not inferred from these theorems.

## Resume audit and terminal lane identification

The WIP snapshot `fc05fed270` contains no proof holes. J10506 checks
`TerminalCallable53.run_success`: retained composition and terminal arithmetic
return successfully with the explicit 29-lane formula. J10508 checks
`TerminalLaneModel53.lanes_eq`: all 29 lanes equal `R0P.SemSource.laneAt`
for the concrete tower basis. Selector marginals and Copy/Poseidon/semantic
lanes are proved rather than supplied. Every accepted printed axiom report
uses a subset of `[propext, Classical.choice, Quot.sound]`.

Receipts J10504–J10508 were recovered from the pinned host workspace after
the capacity relaunch, including rejected drafts and exact source snapshots.
J10504/05 are carrier-transparency drafts replaced by J10506; J10507 is a
selector/variant simplification draft replaced by J10508. `sorryAx` in those
failed elaborations is retained as failed evidence, not an accepted proof.
No unchanged input is replayed. A repository-wide Lean token search outside
evidence finds only 19 comment/documentation mentions of `sorry`; the
100bit-spend-path Lean source tree has zero occurrences.

The terminal theorem still needs the Copy active output identity, selected
claim carrier binding, and actual native caller correspondence. The next
focused step retains the active identity discarded by the prior composition
interface; the current endpoint remains unchanged.
