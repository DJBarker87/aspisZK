# Focused S9 closure attempt — 22 October 2026

The previous S4 library/extraction experiment is held before the new Charon
build. The user asked which S is the quickest credible full-cone attempt with
all four slots. S9 was selected before the S4 adoption, based on its small
four-output, two-side helper and existing 56-coefficient identity. This is a
relative judgment, not evidence that closure is assured. The first decision
point is 4–6 hours, not a promised completion time.

The actual closure target remains the delivery table's complete S9 source
join: reached operands, complete checked helper state/output, surrounding
caller and current source pin, sufficient to instantiate the frozen-order
cone. A successful local algebra/helper theorem alone is not closure.

## Parallel work, with one local compile at a time

- D18: derive the N=4 power trace and exact returned helper arrays from
  canonical seeds. Derive success, indexed canonicality and power meanings;
  do not assume independent successful traces or `kpowers` results. Keep the
  outer caller assignment as a separate source obligation.
- Q: install actual current arithmetic methods in one concrete `FieldOps`
  record, including the selected square body rather than a replacement
  multiply-by-self definition. Supply matching method laws to both workers.
- FS: prove the generated helper's exact two-iteration control/state Result,
  then its success and decoded output using those concrete operations.
  Decompose the actual emitted body; do not copy a nicer algebra model and
  label it the source.
- Root: supply the decoded side-update algebra, integrate the helper with the
  existing factored/original formula, and resolve actual caller/source binding.

Reuse owners include `s3-scalar-factor-powers-constructive-s9-v1`,
`s3-kpowers-total-and-s9-no-premise-v1`, `s3-s9-helper-p6-ops-v7`, the current
field-operation owners, and `S2LibraFactoredIdentity`. The retained helper
source-cut's **Pair method is a normalized candidate**, not the frozen caller.

## New proved component

`evidence/s9-focused-side-updates-root-v1-20261022/` contains
`AspisR1.S9SourceSideUpdatesRootV1.two_side_updates_eq_factored` and
`two_side_updates_eq_original`. They identify the decoded square/multiply
chain, high terms, and exact two-side writes with all four model outputs.
Every old output cell is arbitrary: the complete schedule overwrites them.
Zero challenges are included. No successful-helper hypothesis is introduced.

Focused Lean 4.32 compile: exit 0, 6.576 s, process RSS 1,504,296,960 bytes,
observed swaps 0; standard axioms only. Exact receipt, imports, source pins and
failed first attempt are retained. The original/factored identity is reused.
The current complete helper body matches its retained extracted source-cut
body, SHA-256 `741b0a147a82edfbc47b363e50e5163662cd82be8af21f769699e1d3c9506f2a`.
This is decoded algebra, not yet execution refinement.

## Unresolved boundary and stopping rule

After the S4 adoption, WideExact powers uses the indexed early-return body.
S9 still calls Rust `core::array::from_fn` through QM31 `kpowers` and to build
high terms. Existing P6 models prove ordered value semantics but do not prove
the frozen Rust initialized-buffer, ownership/drop and final array conversion
semantics. The extracted full Pair candidate also does not prove the current
source caller. These cannot be hidden in a record or treated as cryptographic
assumptions.

Do not restart the generic compiler campaign inside this attempt. Establish
how far the concrete helper can be proved, then expose the smallest remaining
library/source obligation. If that boundary prevents a complete cone, report
it and propose a narrow proof-friendly source change with its affected pins
and gates. PR #10 was adopted at `29cbab431` after explicit user approval of up to
12,000 additional CU per transaction. See S4-ADOPTION-DECISION-20261022.md.
This removes the original WideExact powers from_fn obligation; it does not
remove the separate QM31/high-terms library boundary. S9, the global source join, and implementation-linked
100-bit per-attempt soundness remain OPEN.

## Concrete operation progress

The focused concrete record is now green in
`evidence/s9-focused-concrete-fieldops-v1-20261022/`. It installs actual
selected/current operation calls, including the square body, wide product,
add, M31/mixed products and extracted fold. The square and mixed-product
meaning/totality continuation is separate; record dispatch is not counted as
proving those laws.

`evidence/s9-focused-mulm31-total-root-v1-20261022/` closes the previously
success-conditional wide-by-M31 leaf: actual QM and wide calls are now proved
total for every stored input; the concrete S9 record returns a canonical,
exact scalar product on canonical input. No successful multiplication is
assumed. This reuses the existing total U32 reducer and exactness owners.
Focused exit 0, 19.737 s, process peak 3,153,149,952 bytes, observed swaps 0,
standard axioms only. The packet explicitly records incomplete historical
cross-session mutex evidence rather than claiming stronger resource control.

The emitted helper's structural two-step proof, full arithmetic composition,
reached power-array consumer and source/caller boundary remain in flight.
No complete cone has been declared closed.

## Reuse correction and subsequent checked consumers

The generic arbitrary-input M31 totality lemma already existed in
`AspisR1S3PowersLowTotalV1`. The first root packet duplicated its proof;
those primitive lemmas must not be counted as newly closed arithmetic.
The preferred consumer is now
`evidence/s9-focused-mulm31-reuse-root-v2-20261022/`, which directly imports
that owner and proves totality/exactness for the same concrete S9 callback.
The historical first packet has an explicit correction. One focused replay
of V2 repaired missing clean concurrency evidence after a sibling mistakenly
launched a second Lean process; all local launches are now centralized with
ownership/foreign-process monitoring. No unchanged full regression ran.

Further checked packets, all with standard-only theorem audits:

- `evidence/s9-focused-powers-v1-20261022/`: from canonical seeds, construct
  the low N=4 P6 trace/mapped array and actual concrete `kpowers` output;
  all returned entries have canonicality and indexed power meanings.
  Independent low/high successful-call premises are not assumed. The outer
  caller assignment is still separate.
- `evidence/s9-concrete-operation-semantics-v1-20261022/`: actual selected
  square success/canonicality/decode and concrete mixed-product totality.
- `evidence/s9-concrete-wideqm-product-v1-20261022/`: the same constructed
  mixed-product result is canonical and has the exact coordinate products.
- `evidence/s9-wideqm-scalar-product-root-v1-20261022/`: rewrites those same
  coordinate products as multiplication by the QM31 scalar embedding in
  the wide field. No operation-success premise is introduced.

A centrally checked emitted-body control lemma is green in the working
V3 owner: active-body success must return `.cont` with the same next iterator.
Its checked source carve is definitionally equal to the emitted active
suffix. It does not prove body/helper success or decoded output. The
complete two-iteration consumer and high-terms array proof remain in flight.

The generic low-powers source gap has been localized further: the old
full-pair emission declared `weights.powers` externally, and its diagnostic
Rust cut used an unreachable stub. A new narrowly selected NUC extraction
retains the real generic powers function and closure, but its multiplication
shim is still emitted as `fail panic`; that raw output is explicitly rejected
for proof use. A mechanically checked typed-operation/P6 adapter is being
built. No selector retry or compiler rebuild is authorized by this result,
and no frozen Rust Std/array or deployed-compiler correspondence is inferred.

## Adopted-source continuation

The two emitted calls are now proved in
`evidence/s9-emitted-two-step-control-root-v1-20261022/` (commit b8d288ba1):
a successful helper run yields its actual first body call, actual second body
call and terminal iterator result, carrying the same intermediate/final arrays.
This is accepted-run control decomposition, not totality or decoded output.

Current ownership: D18 reuses the generic indexed early-powers theorem for the
actual N=4 WideExact helper array; FS joins the two calls to their actual
scalar-factor results and post-scalar source suffixes; Q joins the four actual
high-term callback results and their exact stateful P6 array; root connects the
checked array writes and branch arithmetic to the retained two-side identity.
Only the root launches local Lean. The shared mutex is respected across other
live Codex sessions; failed attempts and diagnostic axiom reports are not
accepted theorem evidence. No unchanged full replay is launched.

## Concrete execution and candidate-source continuation

The S4 source adoption is recorded in `S4-ADOPTION-DECISION-20261022.md`;
production `weights.rs` is pinned at SHA-256
`28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137`.
The separate S9 candidate below has not been adopted. Earlier statements in
this working log about rejected extraction attempts refer to those particular
attempts, not to the subsequent successful focused candidate extraction.

PROVED local execution links are committed in `f8b20aacb`, packet
`evidence/s9-accepted-execution-links-v1-20261022/`. One successful active
body supplies a shared low/high-power witness and its exact remaining
continuation. The post-scalar continuation exposes the same four term
results, ordered sums and branch continuation. Concrete accepted operations
preserve canonicality and decoded arithmetic of the same returned values.
The second-branch suffix has exact update equations and preserves cell zero.
Input canonicality and checked-source-read premises remain explicit; these
suffix results are not a whole-helper or enclosing-caller theorem.

MEASURED candidate gates are committed in `428a54b5b`, packet
`evidence/s9-explicit-helper-current-gates-v1-20261022/`. The candidate
changes only `factored_s2_libra_weights`, replacing its N=4 power/term array
construction with explicit operations in the same order, including the unused
fourth QM multiplication. Its source SHA is
`9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf`.
The actual candidate native build, SBF build, six fixtures and strict stack
check passed. Against the authorized frozen baseline, stage-1 increases are
at most 10,817 CU and settlement increases at most 8,099 CU, within the
12,000 CU per-transaction allowance. Outputs match on these fixtures.
Legacy B1 and the older +10,000 settlement comparison fail and remain
recorded. These are measurements, not all-input bounds or equivalence proofs.

PROVED concrete carrier transport and compiled generated candidate source
are committed in `8a667eeac`, packet
`evidence/s9-candidate-concrete-adapter-v1-20261022/`. The six raw opaque
operation axioms have been replaced with typed, invertible carrier mappings
to the existing concrete operation owner. Full Result transport includes
failure and divergence. Types, the external definitions and the actual
generated helper compile. The helper, scalar-factor function and generated
Std iterator fold have transitive standard-only axiom reports. Generated
option overrides are removed; namespace qualification fixes a generated
local-variable shadowing error. The raw Aeneas diagnostic files are retained
separately and are not accepted imports. Source extraction success and
compilation do not establish the complete arithmetic specification.

The next composition must preserve the actual source witnesses throughout:
low polynomial meaning, high-term array and source reads, ordered sum
meanings, the q16 power meaning, and the same intermediate/final arrays.
A formula with unconstrained existential sums is only an intermediate
suffix result; it does not close the coefficient relation. A monolithic
side-zero composition hit the default 200,000-heartbeat limit, so it is
being split at the shared-prefix/branch boundary without increasing limits
or changing its mathematical obligations.

OPEN: the complete two-body semantic composition; candidate array/fold/body
transport; actual enclosing caller and relevant library correspondence;
final source/artifact re-pins and S10 integration; the composed security
experiment and raw 100-bit conclusion. No complete S9 cone or 100-bit result
is claimed. Focused receipts reuse pinned warm dependencies and do not
constitute the final coherent release replay.


## Continuation: same-helper branch composition and actual candidate terms

This continuation supersedes the earlier open item for obtaining two branch
execution witnesses from the same successful selected helper loop. Commit
`d46dd805f` proves that join, including the same intermediate array and the
raw cell-zero frame needed to transport canonicality through branch one.
It retains input-read canonicality, and is still a selected-model helper
result rather than a Rust caller or complete coefficient theorem.

Commit `89fc8b853` supplies the second-branch record and actual candidate
scalar callback transport, with a separate standard-axiom audit of the
record constructors. Commit `7188efe5e` derives the candidate body's same
four term child calls from its successful generated-source parent execution.
The exact suffix preserves the already-read PERM index; it does not replace
that index with a fresh read. Commit `469de4f6f` relates each accepted term
to its scaled source coordinate and seed power, using an additive public
decoder export from the original producer. Earlier declaration bodies are
unchanged, but the new owner object is separately pinned.

Still OPEN: compose the same-body scalar and ordered sums into the original
coefficient relation; finish candidate high-array and scalar-fold transport;
join the complete candidate body and outer helper to the model; discharge
actual caller/library boundaries; adopt and re-pin artifacts if the candidate
is accepted; complete S10/coherent replay and the security experiment.
No complete S9 cone or 100-bit conclusion follows from these focused checks.


PROVED continuation: `9d91565e3` derives the scalar polynomial from the same
actual PERM/ap0 reads; `7af29b2dd` derives firstTwo/firstThree/allFour from the
same returned term array and ordered additions. `05ad3ba6b` proves the
candidate's explicit term array maps to the retained callback trace;
`60eb143ab` composes that result with the successful actual generated body,
its exact child calls and its high-array canonicality. These results discharge
local read/term/sum identification obligations; they do not close the complete
candidate body or the four-output coefficient theorem.

Current focused frontier: scalar-fold carrier transport (all fold state and
failure/divergence joins checked in development; constant mapping repair still
pending a fully green target), fixed-index array-update transport for the
candidate branch tail, and separate output-decoder leaves before the final
four-output coefficient composition. Failed elaboration/import attempts are
retained and are not counted as proofs. The frozen production helper remains
unchanged; the explicit-array helper is still a candidate.


The scalar-fold and write-map items above are now PROVED locally in
`0c2c0722f`: the full generated candidate scalar_factor preserves all Result
constructors under carrier mapping to the retained concrete P6 function;
bounded successful array writes return the same mapped output array.
`e827fd13d` joins the actual successful candidate body to the same actual P6
power array, scalar-factor result and ordered term array. This reuses the
previously proved candidate explicit-power array bridge and its retained
fourth multiplication rather than introducing a separate power-array premise.

The complete branch-tail/body join and final four-output coefficient theorem
remain OPEN. Decoder-output composition exposed unresolved conditional
branches; development diagnostics identified those literal branch reductions
as the obstruction behind expensive implicit equality checking. Diagnostics
and failed attempts are not accepted sources. No proof limits were raised.


Further PROVED local obligations: `48fd1096d` checks all five exact output
decoder leaves; `18428eea5` assembles the same candidate prefix into a fixed
P6 body output, retaining the explicit universal same-call `hsuffix` premise;
`4242dda4f` proves the actual generated-candidate two-call loop shape,
with evidence in evidence/s9-candidate-loop-two-call-shape-v1-20261022/.
That statement retains the actual successful candidate loop equation and
derives both same-execution body results, iterator transitions, shared middle
array and returned output without substituting the P6 model.

Still OPEN: the coefficient theorem consuming the five leaves (alias/type
elaboration remains unresolved), the complete ordered branch-tail map and
therefore discharge of `hsuffix`, complete helper/caller/library refinement,
source adoption and final artifacts, S10/coherent replay and composed security.
The conditional assembler is not a full-body correspondence theorem. All
checks above are focused warm-cache compiles with standard axioms only; no
production code was changed and the 100-bit target is not yet established.


PROVED selected-model arithmetic milestone: `9cef9deb3` composes the two
same-execution body witnesses into all four factored S2 coefficients, then
reuses the existing `original_eq_factored` theorem to derive the original
S2 coefficients for a successful selected P6 helper loop. Both challenge
seeds are tied to that execution's actual extra[0]/extra[1] reads. The
explicit canonical-read premises and selected-model boundary remain.
Evidence: evidence/s9-selected-helper-original-coefficients-v1-20261022/.

PROVED transport progress in `cc8aaba3b`: the actual generated-candidate
loop maps to the concrete P6 loop conditional on the explicit same-call
suffix transport premise and canonical reads. The complete ordered term
prefix separately preserves Result and the exact first2/first3/all triple;
no successful sum or desired output equality is assumed. The second-branch
ordered tail transport is checked in `015ba86bf`.

Current implementation-join frontier: compose the checked sum prefix with
both checked tails at actual candidateAfterTerms/p6AfterTerms, including
Result bind association and branch dispatch, then discharge the conditional
loop/top wrapper's suffix premise. These checks do not establish candidate
adoption, frozen Rust/library/caller refinement, final artifact binding,
S10/coherent replay or the composed security experiment. No whole S9 closure
or 100-bit result is claimed. Production source and CU are unchanged.


PROVED candidate-helper milestone (supersedes the open suffix/coefficient
items above): `049163e113` derives all four original S2 coefficient equations
and all four canonical returned cells from the actual generated-candidate
helper success and explicit canonical-input conditions. The universal suffix
transport is constructed from the actual same-call continuation: `hsuffix`
is no longer a theorem premise. Actual extra[0]/extra[1] reads bind both seeds.
`e56f92fb53` pins this result specifically to attempt-2 candidate source
SHA 9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf;
it does not apply to the source-only 9ce draft or unchanged production helper.
Evidence: evidence/s9-candidate-helper-original-coefficients-v1-20261022/.
Both commits are pushed on research.

RETAINED: successful helper execution and canonical caller/challenge reads.
Next proof work constructs successful execution from canonical inputs, reusing
existing extracted-fold and concrete arithmetic totality. Side one needs a
canonical old cell 1; side zero establishes that invariant for the second
iteration. The real caller, deployed Rust/Std correspondence, candidate
adoption, frozen artifact binding, S10/coherent replay and composed security
experiment remain OPEN. These focused checks do not close S9 or establish
the 100-bit target. No production code or CU changed.


Further PROVED constructive obligations: `7bdc43083a` derives actual
generated-candidate scalar_factor success from canonical mapped inputs,
and concrete QM31 multiplication success/canonical outputs from canonical
operands. `eacf92b8d0` constructs the selected side-zero arithmetic prefix.
`adb840ed37` constructs all four actual candidate power multiplies and proves
the selected arithmetic prefix for either bounded side, with no child-call
success premise. Existing extracted-fold, power-array and exact arithmetic
owners are reused. All focused checks passed below 3.3 GB with zero observed
swaps and standard axioms only; immutable failed elaboration attempts are not
counted as proofs. See the three corresponding evidence packets.

The current constructive frontier is joining the canonical high-term array,
its exact from_fn result and sums, both branch tails and the forward loop
constructor. A NUC caller-step extraction is candidate evidence in progress;
its field-decoder and accumulation interfaces must still be discharged. No
caller/refinement or release/security closure is inferred from that extraction.


PROVED complete selected helper-loop construction: `527c302de5` constructs
both actual selected activeBody executions, the actual fixed iterator
transitions, and the complete loop success from canonical ap0/ap1/extra reads.
The initial array can be arbitrary: side zero establishes the canonical
cell 1 required by side one. No loop/body/child success premise remains in
`selected_helper_total`. Evidence:
evidence/s9-body-and-loop-construction-v1-20261022/.

PROVED selected correct-result composition: canonical reads alone construct
the zero-initialized helper result, canonicality of all four returned cells,
and all four original S2 coefficient equations with actual challenge-read
witnesses. Evidence: evidence/s9-selected-helper-correct-result-v1-20261022/.
It reuses the existing successful-run canonicality/frame and coefficient
owners, rather than duplicating their proofs.

The generated candidate's successful-run correspondence was already proved,
but cannot be reversed to infer candidate success. Candidate term construction
is now separately checked: one actual selected callback witness constructs
the corresponding actual candidate term call using full Result operation
maps; all four calls follow from the same HighTermsFour witness. Its complete
prefix/body/loop construction is still in progress.

Caller-step integration found two different compiled owners for byte-identical
QuadraticTowerOperations and QM31WordResidues sources in the old S3 parser
and current S9 caches. The remaining common objects match. This does not
authorize silently mixing cohorts: a focused S3 dependency-frontier rebuild
against the selected S9 owners is being prepared on the NUC before composing
the field-readback adapter. No coherent release replay is claimed.
