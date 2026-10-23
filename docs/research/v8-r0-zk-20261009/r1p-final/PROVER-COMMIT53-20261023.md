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

## Stage 3: complete retained terminal value

J10510 preserves the Copy active output's model identity in
`PreparedCopyComposition53.components_and_tail`; J10511 composes it with the
concrete Poseidon callable and actual caller-selected variant/index. J10513
proves the row-major claim/opening and decoded-point bridges. J10517 proves
`AspisR1.TerminalModel53.run_success`: for canonical 84 claims, point,
zerocheck point and challenges, and the original successful public preparation,
the retained terminal continue branch succeeds canonically and its decoded
first output equals **`R0P.SemSource.terminalValue`** on those actual claims
and points with `ProverCommitQBasis51.basis`. No Poseidon, semantic, Copy,
active-output or terminal-value image is assumed. The 29th claim column is
zero-extended, and terminalValue never reads that column. This is the retained
source cut; native entry validation and native optimized-call binding remain.

J10509 is a rejected placeholder draft; J10512 a numeral-bound/extensionality
draft; J10514–16 are alias/transparency drafts. J10516 reaches the unchanged
200000 heartbeat limit; J10517 replaces unfolding with opaque model operations
and symbolic selector equalities. No limit is raised and no unchanged attempt
is retried. Every accepted new theorem prints only standard axioms.

| Attempt | Target | Exit | Wall (s) | Peak RSS (KiB) | Swaps |
|---|---|---:|---:|---:|---:|
| J10510 | PreparedCopyComposition53 | 0 | 1.63 | 4167788 | 0 |
| J10511 | CompositionDetailed53 | 0 | 1.74 | 4210592 | 0 |
| J10513 | TerminalClaimModel53 | 0 | 1.65 | 4237780 | 0 |
| J10517 | TerminalModel53 | 0 | 5.38 | 4242328 | 0 |

Exact target names, source hashes, dependencies, complete axioms, failed
diagnostics and GNU-time fields are retained in `lean/J10509`–`J10517` receipts.
The receipt revision `1fb1793c05` denotes the unique parent commit of this
stage; each receipt separately pins the exact compiled working source.
No preexisting shared source/object is overwritten. The endpoint and shipped
sources are unchanged.

## Stage 4: complete gamma batch and coefficient provenance

The new `gamma-owner` is an explicit counter cut of the native selected-j
29-lane fold and 1024-output map. Charon/Aeneas run optimized and capped:
exit 0/0, wall 1.48/0.346 s, peak RSS 205580/67056 KiB, swaps 0/0.
The extracted arithmetic declarations are compared byte-for-byte before
reuse; `gamma-callee-binding.json` records every reused declaration and exact
new declaration. No external template or trust field is added.

J10524 proves the complete source matrix cell equals the established
29-lane arithmetic owner. J10526 proves the entire 1024-cell update interval,
including preservation outside it. J10527 composes one shared gamma-power
producer with all 1024 cells. J10529 identifies that result with
`Batched.batchR1` given coefficient provenance. J10530 discharges that
provenance with actual per-column `coefficients51.eval` Results via
`ProverCommitGammaCoefficients53.column_spec`; its `exact_result` concludes
the complete batch image without an assumed coefficient-array/model identity.
The input is arbitrary canonical tape columns (the trace is defined from
them), with the existing source gamma/challenge representation `value x =
ch.opening 0` retained. Native Vec allocation/map assembly and complete
Weights construction are separate, not inferred from the owned counter.

J10518 is retired without compiler invocation after a missing private source
directory prevented upload; J10519 then checks the extracted declarations.
J10520 exposes duplicate ZERO from the binding script; J10521 reuses the
retained Pairs declaration. J10522/23 are sequencing/numeral-bound drafts,
J10525 a copied-loop draft, and J10528 a missing rowEquiv import draft.
Accepted proofs all print only standard axioms. No source is retried unchanged
with the same dependencies; no shared object is overwritten.

| Attempt | Target | Exit | Wall | Peak RSS (KiB) | Swaps |
|---|---|---:|---|---:|---:|
| J10519 | AspisR1ProducerRelease47.GammaBatch53 | 0 | 0:01.09 | 2638016 | 0 |
| J10521 | AspisR1ProducerRelease47.GammaBatch53 | 0 | 0:01.11 | 2635176 | 0 |
| J10524 | R1Z.ProverCommitGammaCell53 | 0 | 0:02.34 | 4115024 | 0 |
| J10526 | R1Z.ProverCommitGammaFill53 | 0 | 0:02.11 | 4104640 | 0 |
| J10527 | R1Z.ProverCommitGammaOutput53 | 0 | 0:01.92 | 4103140 | 0 |
| J10529 | R1Z.ProverCommitGammaModel53 | 0 | 0:02.05 | 4135164 | 0 |
| J10530 | R1Z.ProverCommitGammaCoefficients53 | 0 | 0:01.97 | 4253916 | 0 |

Exact source hashes, dependencies, revision, rejected errors and all printed
axioms are in `lean/J10518`–`J10530` receipts. Native trace diagnostics are
recorded separately and are not yet accepted evidence for the caller. The
whole-29 trace diagnostic was stopped during Kani report processing at
6568672 KiB RSS (276.747 s, zero swap), without raising caps. It is replaced
by a universally quantified one-iteration trace check; the Lean induction
already covers the full arithmetic sequence.

## Stage 5: actual owned point claims

J10531 checks a new extracted 29-column/three-point owner, whose unchanged
MLE and statement-point declarations are reused only after byte equality.
J10532 proves every column read succeeds canonically with its exact MLE value.
J10534 proves `R1Z.ProverCommitClaims53.exact_result`: for arbitrary canonical
point and tape columns, all **87 source claim outputs** equal
`honestClaims (trace columns) (decoded point)`. Successor/absorption points,
column evaluations and the complete three-row assembly are conclusions,
not caller-supplied images. Native `host_semantic::point_claims` allocation,
error layers and Vec iteration still need their separate source binding.
J10533 is a tuple-normalization draft replaced by one `rfl` on the tiny
three-element constructor. Accepted axioms are standard only.

Claims Charon/Aeneas: exit 0/0; wall 1.276/0.478 s; peak RSS
210196/69872 KiB; swaps 0/0; source revision `d015ebd5b5` plus exact owner
and generated-source hashes in the binding manifest. J10531: 1.23 s,
2637620 KiB; J10532: 2.54 s, 4129916 KiB; J10534: 1.86 s, 4152672 KiB;
all exit 0, zero swaps, capped at 6G/8G/no swap/64 tasks.

The gamma selected-operand native check passes (`gamma-native-v7`): exit 0,
0.441 s, 130400 KiB, zero swaps, explicit Rust opt-level=3. It pairs arbitrary
multiply/add answers with identical ordered operands; it does not prove
field arithmetic, matrix reads, allocation, or the complete native caller.
Those distinctions are explicit in the source pin. Earlier diagnostics and
all source snapshots are retained: v1/v2/v6 are CLI preflight refusals; v3
reports the memcmp unwind limit; v4/v5 are stopped report-processing growth
(6568672/6627632 KiB, zero swaps). No cap is raised. v7 changes to the
selected-operand interface and disables assertion-reach reporting.

The current Weights constructor extraction is a separate work-in-progress
continuation. J10535 is retired before compilation for a wrong retained
module path; J10536 uses the actual retained inactive-source import.


## Stage 6: stored Weights and complete materialization

The second resume recovers host receipts J10536–J10554. J10537 checks
extracted Weights declarations; J10546 proves storage/row reuse; J10551
proves `ProverCommitWeights53.exact_result`. J10550 checks the extracted
materialization owner. Rejected drafts are retained verbatim. J10549 has
no compiler receipt and is retired unused, rather than reused.

J10554 failed on the zero-counter case: the unfolded condition was already
`True`, so a scalar-equality simp rule did not close it. J10555 replaces
that rule with `ite_true`. All three binding theorems then compile with
exactly `[propext, Classical.choice, Quot.sound]`, exit 0, wall 1.81 s,
peak RSS 4147356 KiB, zero swap. No literal sorry was present; the failed
elaboration had inserted `sorryAx`. The accepted replacement has none.

J10556 exposes omitted section hypotheses in the unfinished top theorem;
J10557 explicitly includes canonicality hypotheses and proves
`ProverCommitWeightsMaterial53.exact_result`: a single initialized object,
all five stored factor matrices, all 1024 rows, and all seven kappa terms
produce canonical materialized outputs with the complete wide-row model
value. No stored factor or raw table image is assumed. J10557 exits 0,
wall 2.07 s, peak RSS 4156548 KiB, zero swap. All four printed theorems
have exactly the standard axiom set. Revision `bb69037133` plus the exact
source/dependency hashes in receipts identifies these inputs.

The separately recovered `weights-storage-native-v1` Kani check succeeds:
exit 0, wall 98.31 s, peak RSS 4631592 KiB, zero swap, explicit opt-level=3,
6G/8G/no-swap/64 scope. It verifies the unsafe allocation/write layout on
successful reserve for arbitrary producer outputs. Allocation failure is
retained as an error; this cut does not prove the full native constructor
or connect native arithmetic producer calls. Complete payload equality
remains open, and the deployed endpoint remains unchanged.


## Stage 7: opening cells and ordered bytes with producer provenance

J10558 identifies stored materialization with `Batched.weightsR1` on the
same decoded challenge inputs. J10559 composes this with the complete
coefficient/gamma producer and the owned two-round opening kernel. J10560
identifies the primal fold with `Batched.q1` and both round/final outputs
with the exact `BatchedLayer.read` cells. J10561 adds the complete ordered
7/7/64 byte images. These are new conclusions of one composed retained
caller; no batch-array or weight-array model image is an input.
Caller challenge representation identities remain explicit, as do the
separate native Vec and entry/callee binding obligations. The folded leaf
encoding and semantic caller remain open; this is not full payload equality.

All four attempts exit 0, zero swaps, 6G/8G/no-swap/64 tasks; printed axioms
are exactly `[propext, Classical.choice, Quot.sound]`. Wall/peak RSS KiB:
J10558 2.45 s/4148684; J10559 2.48 s/4277956;
J10560 3.30 s/4277740; J10561 3.78 s/4280180.
Receipts identify revision `11b5c5c38e` and exact changed-source/dependency
hashes. The endpoint remains byte-identical and retains RustProverRefinement.


## Stage 8: native inverse fibre transform and direct encoder obstruction

J10562 proves full eight-limb WideExact subtraction. J10564 checks the
selected `encoder53.phi_inverse` extraction (J10563 omitted its retained
Basis import and is rejected). J10570 proves success, canonicality and all
four values for arbitrary canonical wide x/y and channels. J10571 proves
its algebraic image is exactly `FirstFold.fibreEvaluate`, including slot
order. `encoder-native-pins.json` checks the native generic function and
specialized owner bodies agree after whitespace/trailing-comma normalization;
both Rust field files are byte-identical to the native files. Only the
phi declaration and byte-identical retained arithmetic are imported. No
external template is installed and no new trust field is added.

J10565 is a numeral-argument simplification draft. J10566–68 expose a
concrete field-instance elaboration timeout at the original 200000
heartbeats. J10569 replaces Field in the purely syntactic phi formula with
its actual Add/Mul/Sub requirements, avoiding reduction of the concrete
field hierarchy. It leaves four redundant `rfl` commands after goals close;
J10570 removes those commands. No limit is raised and no unchanged input
is replayed. Every accepted axiom report is standard only.

| Attempt | Exact module suffix | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10562 | R1Z.ProverCommitWideSub53 | 0 | 1.63 | 4090744 | 0 |
| J10564 | AspisR1ProducerRelease47.EncoderPhi53 | 0 | 1.09 | 2635468 | 0 |
| J10570 | R1Z.ProverCommitEncoderPhi53 | 0 | 3.27 | 4117860 | 0 |
| J10571 | R1Z.ProverCommitEncoderPhiModel53 | 0 | 3.79 | 4116160 | 0 |

Receipts pin revision `418ec0676e` plus exact source/dependency hashes;
all compiles use the 6G/8G/no-swap/64-task scope. The five phi theorems
print subsets of `[propext, Classical.choice, Quot.sound]`.

**Demonstrated direct-source obstruction:** the exact specialized native
`eval_rec` iterator/Vec body extracts in v3, but Aeneas emits external
axioms for Copied/Skip types, constructors and next methods. v5 selectively
extracts the constructors but still emits opaque types and next methods.
Broad body extraction v4 and monomorphic body extraction v6 both set
Charon's `has_errors` with mismatched iterator trait clauses; the driver
stops before Aeneas. Their Charon exit code is 0, which is explicitly NOT
accepted as a successful translation. No opaque adapter is admitted.
v1/v2 are Rust specialization preflight errors, corrected in v3.
All attempt receipts, input hashes and diagnostics are retained under
`encoder-diagnostics/`; the v3 templates are diagnostic `.lean.txt` files.
Every extraction job is optimized and capped, zero swaps; exact tool
pins, wall/RSS and error output are retained. Aeneas v3/v5 exits 0 but its
external templates prevent an accepted source-recursion theorem.

Consequently native eval_at/encode_at, exact nodes_for geometry and
opened/folded leaf images remain unproved. Repairing the iterator adapter
extraction (or proving a source-equivalent explicit collector) is the next
concrete deliverable. The phi result alone does not establish the leaf
encoder. Remaining semantic guards/interpolation/whole native caller and
complete simulator payload equality are also open. The target is not yet
established; no FSExperiments conversion or join is attempted.


## Final coherent import/axioms audit and handoff

J10572 (`R1Z.ProverCommitAudit53`) imports all 30 part-53 live modules
in one environment and prints all 58 public new theorem axioms plus the
unchanged deployed headline theorem. Exit 0, wall 1.73 s, peak RSS
4397276 KiB, zero swaps, source revision `7cbabb93ed`, 6G/8G/no-swap/64
limits. All 59 reports use only subsets of
`[propext, Classical.choice, Quot.sound]`; **no sorryAx remains in the
accepted results**. This is a coherent import/axioms audit against the
retained dependency closure, not a complete frozen-manifest release replay.
No unchanged regression is repeated and no release result is claimed.

`final-manifest.json` pins every root and theorem; `final-integrity.json`
checks each live root source matches a successful compile receipt, scans
all 31 changed/live audit Lean sources for forbidden proof tokens, and
confirms no shipped crates/programs file changed from task base
`3bf0a58481bc98110878803c3d8aacfec2371375`. The endpoint before/after
snapshots are byte-identical. No ELF rebuild is triggered; no wallet/key
is touched. No binary, LLBC, olean or archive is committed.

**Stop:** the demonstrated encoder adapter extraction obstruction in stage 8
prevents the actual native leaf-encoding refinement on this pinned toolchain.
No new external axiom is accepted to bypass it. Native simulator output =
`R0Z.RefPayload.simE` payload remains unproved. Semantic caller guards,
interpolation/original-round provenance, native constructor/Vec bindings,
challenge representation, node geometry and leaf images remain explicit
continuation work; the retained terminal, owned complete batch/weights,
opening cells/bytes and native phi results do not discharge them.

The next free compile number is **J10573**. J10573–J10599 are untouched;
J10518, J10535 and J10549 are explicitly retired without compiler invocation.
Continue only with changed source/dependencies; do not replay a failed
unchanged source, raise limits, install the rejected templates, or infer
complete payload equality from the accepted local results.
