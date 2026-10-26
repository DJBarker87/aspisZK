# rw17 resume: whole-loop context and data join

Base `c4eb7e74cb`, branch `codex/cx-prover-rw-20261023`.
Allocation: 100 Lean invocations, 20 Kani harness runs; Env-J IDs25900–26199.
No shipped source, wallet key, release pin, sibling worktree, or shared launcher is modified.
The target is not yet established.

## Stage 1 before / intended after

Before: rw17 proves the combined emitted transition's complete iterator loop
and arbitrary-slice compression equal the closed owned reference. The original
helper's full-source association and the live op223 join are absent.

The new inline-context declarations explicitly separate an arithmetic-inlined
for-loop context from the combined step's Boolean interface. The intended
induction retains all continuing accumulator/power state and projects only the
terminal accumulator. These declarations are **not** claimed to be an extraction
of the original helper. The sibling-owned source identity must still be supplied.
No endpoint or ledger row is discharged by introducing a context definition.

## Ownership and concrete model

Read-only `git grep -l op223 codex/pv-cb3-20261026 codex/pv-cb-20261026`
was run before stage1. pv-cb3's ROWS.md lists op223/V240 OPEN; no Op223Source
module was present. Its source law is reserved to that worker.

The read-only runjoin SourceConstructor/SourceBoundary modules expose a partial
runtime with world, policy, native inputs, disclosed/oracle projections and ideal
handler parameters. CanonicalFixtures proves mathematical nonempty fibres while
retaining the native public-record associations. They do not provide V163's
concrete source/model byte-and-audit comparison. Clarification on the intended
pinned instance is pending; no model is defined as the actual output merely to
make the equation reflexive.

## Validation discipline

Each focused local compile uses the retained pinned J object cache, Lean4.32
-M7000, and no dependency build. The immutable input/receipt pair records source
revision and hashes, imported object fingerprints, target, exit, wall, RSS, swap
and complete axiom reports. This is focused cached evidence, not a coherent
release replay. Failed elaborations and their error-generated sorryAx output
are retained as failures, never imported as accepted evidence.

25901 was a dependency preflight refusal; it invoked no compiler and costs zero.
KANI-PLAN.json lists all candidate harness names before any charge. Bounds2/3
cover loop-free/one-element contexts; bound18 exceeds the proved17 arity16
iterator evaluations and covers the finite16-element array conversion. Each
native run uses the existing host runner with6G/8G/swap0/Tasks64, one host scope
at a time, optimized Rust and unwinding assertions. Special-value gates retain
their restrictions and do not imply an arbitrary-input certificate.

Host admission004 refused at18:33:26.823899UTC (60,532,195,328 bytes
reserved;69,122,129,920 projected >59,055,800,320 safe). No scope/compiler
started. Retry004r1 was after18:36:26.823899UTC and was refused again.
Both are zero charged Kani runs; next retry waits at least180s from004r1.
The intermediate remote Python quoting error invoked no harness or scope.

## Stage 1 checked result

`ProverRw18ContextInduction.run` proves the inlined context equals terminal
projection of the emitted-step iterator for arbitrary slices, positions,
accumulators, powers, lambdas and primitive dictionaries, including all Result
branches. `ProverRw18ContextReference.compress` links that context to the indexed
extracted P6 reference without selected-arithmetic assumptions.
`ProverRw18ContextCompression.owned` then specializes to closed current arithmetic.
`ProverRw18ContextFuel.arity16` proves17 sufficient; `ContextTotal.paired_total`
proves inhabitance for any two typed16-tuples with no success hypothesis.
This last theorem has not yet identified the actual native fixture tuples.

The exact retained join obligations are visible in `ProverRw18ContextJoin.callback`:
`source_law : ops.op223 = extracted` and
`context_identity : extracted = @ProverRw18ContextCompression.compress _
(PV_CurrentScaleInstall.selected ops)`.
Neither is proved by the new theorem. V164's mathematical context is reduced;
its original-source association and V240 source law remain OPEN. V163 remains
OPEN with exactly its original whole-data premise. No endpoint/deployment
premise removed, renamed, weakened or silently bundled.

Validation through25913:13 charged Lean checks,10 passes/3 elaboration failures;
all accepted axiom reports are standard. 10/20 Kani gates pass so far, with
no failing comparison and no timeout. Full individual receipts are retained.
The final cached manifest/axioms audit will run once after the source stages.

## Stage 2: actual fixture measurements and consumed data criterion

The optimized native fixture comparison passed in `pv-rw18-fixtures-004`:
816 comparisons for transfer and816 for withdrawal, each over136 original
copy-registry links, producer/consumer tuples, and three lambdas. The driver
compares the actual shipped compression, the immutable literal snapshot,
the indexed owned reference and the emitted combined transition; it also checks
all16 active steps, empty terminal iterator and the final power. Nonzero tuples:
270 transfer and264 withdrawal. This is finite native measurement, not a
universal source proof or a proof-byte/audit security-model comparison.

`ProverRw18FixtureSamples` reifies one measured tuple for each fixture and
uses named symbolic general theorems for equality and nonempty output.
It does not evaluate the large recurrence in the kernel. The generator has
`--check`, and records both stdout and generated-source hashes.
`ProverRw18ContextCaller.caller` consumes the context join through the full
caller. `ProverRw18ContextData.refinement` consumes the proved writeback,
but retains source_law, context_identity, proof_bytes and audit_data explicitly.
The before/after for V163 is unchanged: neither actual data comparison is
proved, and no arbitrary model is defined as the actual body output.
`ProverRw18ContextErrors` checks that even the final multiplication failure or
divergence remains observable. `ProverRw18ArithmeticBounds` proves raw scalar,
canonical scalar and unreduced complex-product width bounds symbolically.

The first fixture compile failed because the diagnostic fixture module was
feature-gated; only the proof-local manifest was corrected. Both earlier
admission refusals and that exact failed source are retained. No shipped
source or feature definition was edited. The fixture flag is explicitly
`insecure-spend-fixture` and supplies deterministic diagnostic witnesses.

## Original source extraction probes

`extract-original.py` targets the actual `aspis_statement::logup` function in
the frozen crate, not the proof-local snapshot. Charon optimized-MIR probe001
succeeded (16.46s,653436KiB RSS,zero swap). Its333893-byte LLBC root is the
original function at logup.rs75–83; SHA256
`74113d7473e504860141ea6f017f35c35bf7d6b840453d0d55c4463975af67be`.

Aeneas001 (strict joins) and002 (forced Std loop with branch duplication)
both fail at `InterpReduceCollapse.collapse_ctx_following_sequence` line1991
with Not_found before an original helper definition is accepted. Probe003r1
is a CLI rejection: the Lean backend does not support `-use-fuel`; it is not
an extraction or a theorem. Probe004, forced recursive extraction without
fuel, again fails at the same symbolic loop-context join. No emitted failed
root or external axiom template is imported. The installed backend and shared
infrastructure are untouched. A monomorphized frontend probe is planned to
isolate the generic iterator context; its first admission was refused.

Kani014, `canonical_scalar_mul`, times out240s on its tightened canonical
input domain. It supplies no certificate and will not be rerun unchanged.
The original scope is gone; no orphaned scope is deliberately overlapped.

Native receipts pin ambient unrelated files too. `native-source-validation.json`
asserts equality only for the actual task crates and proof-local dependencies;
it does not claim equality of unrelated cost-probe source or rw17's unused
Cargo.lock, nor a coherent release/dependency build. Kani's bundled compiler
identity is not inferred from the receipt's ambient `rustc -Vv` field.

### Per-step cadence deviation

Kani012 `zero_lambda_16` checks a restricted whole-helper arity16 execution.
Although it completed in6.93s and is not used as the universal correspondence
certificate, this exceeded the user's **per-step-only Kani** instruction.
It remains charged and retained as a procedural deviation; it is not relabelled
as a per-step proof. No remaining planned Kani harness executes more than one
arithmetic source step. The optimized native fixture differential is separately
classified as measurement and does not consume a Kani source-association claim.

### Pinned frontend disappeared

The partial-monomorphization probe `pv-rw18-original-mut-charon-001` did not
invoke Charon: Python raises FileNotFoundError for the previously used pinned
`/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon`.
No replacement tool, rebuild, launcher repair or cap change is attempted.
Per local-lean rule5 the lead owns infrastructure repair. Local proof work
continues; this bootstrap failure is not a source counterexample or a charged
Lean/Kani run. The earlier LLBC/emissions/receipts remain the evidence inputs.

## Checked arithmetic/model and source-initializer continuation

`ProverRw18FieldMeaning`/`FieldStep`/`FieldFold` derive the field value and
canonical state of the closed source loop. `FieldCompression.owned` and
`FieldReference.closed` prove equality to a polynomial plus a canonical
coordinate encoder, rather than assuming a returned-output equation.
`FieldStateReference.combined` includes the complete accumulator/power state.
The field-value domain is explicit: canonical initial registers and lambda;
compression additionally needs tag<P. Tuple elements remain arbitrary raw U32.
These extra conditions belong to the additional mathematical value theorem;
the earlier unrestricted source/reference Result equality is unchanged.
The component reference is not V163's whole proof/audit model.

The isolated actual logup::lift initializer extracted successfully through
Charon and Aeneas. `ProverRw18OriginalLift.initial` uses the existing selected
constructor meanings; `ProverRw18LiftTyped.transport` additionally retains the
literal emitted nominal type definitions and proves the explicit Full-carrier
transport, including primitive failure/divergence. Four nominal round trips
have no axioms. No external axiom template is imported. The original full
for-loop extraction and op223 source law remain open.

The complete Kani allocation is now20/20:16 passes and4 timeouts
(014,015,016,020). No counterexample, timeout promotion or unchanged timed-out
rerun. No further Kani invocation is authorized in this allocation.

## Stage 3: existing compression polynomial and Copy registry

Before: `FieldReference.value` used an independently defined Horner recurrence.
After: `ProverRw18CopyPolynomial.value` identifies it with the existing
`R0P.compressPoly` arity16 polynomial. `CopyReference.closed/context` return
its exact canonical encoding, and `CopyTaggedReference` discharges tag<P
for every member of the frozen136-entry registry using `copy_tags_indexed`.
`CopyWide.value` maps this identity into the headline WideExact field through
the existing algebraMap; no smaller field is substituted for that carrier.
`FieldSuffix.field` covers arbitrary iterator positions, including exhausted
positions, and `FieldPowerPure.projection` needs no ExternalTypes instance.

All are component theorems: the original-root identity and op223 source law
remain arguments to `ContextJoin.callback`. Both V163 data comparisons and
the concrete whole model remain absent. The earlier native816 comparisons
per fixture are the non-vacuity measurement; `FieldFixtures` separately
specializes the mathematical reference on the two measured sample tuples.
No endpoint premise is removed.

Focused failures25937/25940/25944 exposed normalization/recursion limits at
the concrete field bridge. The replacement isolates generic Horner algebra,
a scalar specialization, and unfolds the tuple before applying that theorem.
No recursion/heartbeat cap was raised.25945--25949 are green with standard
axioms only. Exact snapshots, statuses, wall/RSS/swap/revision and axiom lines
are in their receipts. Sibling op223 remains OPEN on the stage5 read-only
branch inspection.
