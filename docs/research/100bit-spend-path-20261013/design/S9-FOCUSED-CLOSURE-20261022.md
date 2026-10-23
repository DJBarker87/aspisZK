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


PROVED generated-candidate helper total correctness (candidate weights SHA
9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf).
Canonical input-read contracts alone now construct the actual candidate public
wrapper success, all four canonical output cells, actual challenge witnesses
and all original S2 coefficients. No helper/body/suffix success premise
remains. Side zero establishes the old-cell canonicality required by side one.
Eight focused modules passed with standard axioms, zero observed swaps and
below 3.3 GB aggregate RSS. Evidence:
evidence/s9-candidate-helper-total-correctness-v1-20261022/.

The NUC selected-owner parser frontier has also compiled successfully; its
receipts are being packaged separately. This is a focused frontier rebuild,
not the complete coherent release replay. A new exact-source decoder cut
transparently extracts the actual field/from_le_bytes/from_limbs bodies;
extraction success is not yet a Lean source-refinement theorem. The earlier
caller projection's stubbed field is not treated as actual field identity.
Actual caller/source and Rust library correspondence, adoption/artifact
binding and security composition remain OPEN. S9 release closure and the
100-bit target are not yet established. Production source and CU unchanged.


PROVED decoder source-body chain (2026-10-22 continuation): the source-pinned
owned copy of the actual field decoder maps to the existing parser for every
from_limbs/from_le_bytes Result, including rejections and divergence.
Successful execution of the owned weights.field body yields its exact
range-selected slice, 32-byte length, eight limb bounds and unchanged packed
value. The successful reader result is also canonical in the retained
current-finish/current-wide carrier, without assuming an old decodeField
wrapper succeeds. The canonical consumer passed locally with standard
axioms, 24.523 s, 3.17 GB aggregate RSS and zero observed swaps; its packet
is being prepared. Exact readback and decoder packets are committed:
8ba65b7b45 (limbs), 2712ef9b7d (bytes), f656b659e1 (reader).

The selected parser owner frontier passed on the NUC (19 changed targets,
one accepted owner reused); this is not a whole release replay. The bounded
range source-value model now agrees with Aeneas next, with explicit two/four
iteration tables and no assumed step results. Pinned Rust source snapshots
have matching fold/range bodies. This does not identify the SBF compiler
binary or prove compiled operational correspondence (2c9037de54).

OPEN next: attach the proved actual reader to the caller adapter (whose old
chosen decodeField wrapper is still distinct), prove caller-helper carrier
simulation, establish bounded-index/readback correspondence and actual caller
reachability, then adoption/frozen source and artifact joins, coherent release
replay and security composition. No source-only 9ce draft or unchanged
production helper inherits the candidate 933 theorem. No new CU measurement
or production source change occurred. S9 release closure and the per-attempt
100-bit target remain not established.


PROVED actual-reader-backed caller slot: e197a8bf4e replaces the chosen old
decodeField slot in a distinct candidate adapter with the source-pinned owned
reader and an explicit nested carrier map. Successful calls supply that same
reader execution, source-selected bytes, eight canonical limbs and canonical
selected P6 values. No old decoder-success premise remains in this adapter.

PROVED bounded checked/wrapping agreement: the unchanged V8 R152 generic
lemmas were compiled against the selected cache and reused. For i.val < 48,
the owned reader equals the checked generic reader with the exact same
decoder and bytes. The small bound was explicit in that local theorem.

PROVED caller BODY discharges the index bound: a successfully continued
selected projection body contains a same-execution libra[j] read from the
four-element array, forcing j.val < 4. It therefore yields canonical actual
field output and checked-reader agreement at that same j without an assumed
iterator invariant or caller-provided index bound. Evidence:
evidence/s9-pair-projection-field-bounds-v1-20261022/.
Focused check: 23.345 s, 3.20 GB aggregate RSS, zero observed swaps, standard
axioms. This is the exact selected projection body; full production caller
identity and whole-loop/refinement composition remain OPEN.

The NUC helper-carrier transport is being rebuilt against this actual-reader
adapter cohort. A genuine helper/projection Rust cut using actual core types
is in preparation to replace the earlier fake-carrier extraction boundary.
There is still no S9 release closure or composed 100-bit security result.


PROVED selected projection dot-step: the same successful body execution
supplies the source field/coefficient reads, product, addition and returned
array update. The actual field read is canonical; selected concrete
multiplication/addition preserve canonicality and prove total = old + field
* coefficient under decoding. Canonical accumulator and coefficient reads
remain explicit caller contracts. Evidence:
evidence/s9-pair-projection-dot-step-v1-20261022/.
Focused result: 21.098 s, 3.24 GB aggregate RSS, zero observed swaps,
standard axioms. This is a source-cut BODY result, not whole-loop or full
production source/refinement closure. The helper transport and genuine
actual-core-type Rust cut remain in progress; the 100-bit target remains
not established.


Genuine actual-core-type Rust cut feasibility is now GREEN: Charon and Aeneas
translate the exact candidate helper, real field reader/decoder and selected
projection with the actual copied core field types. Six arithmetic methods
and the non-S2 twofold function are explicit opaque boundaries; the S2 helper,
reader and projection are transparent. Source-only extraction evidence:
evidence/s9-helper-actual-field-types-cut-v1-20261022/.
The raw generated Lean remains diagnostic, not an accepted proof or axiom
source. Correct selectors use a wildcard for the inherent impl path component:
the pinned Charon matcher does not implement explicit inherent-impl matching.
Existing successful helper command settings were reused to avoid the Rust
1.98 Try-trait model mismatch from overly broad standard-library includes.

All six actual arithmetic method source bodies match retained extraction
inputs used by the chosen semantic owners. WideExact mul/add/mul_m31 reuse
S1/S3 exact arithmetic; mul_qm31 uses the qualified S3 generated-source model.
QM31 mul inherits currentQMOps; square uses actualQMSquare and its retained
selected-mask extraction. Exact source/tool/owner references and the residual
new-cut opaque-call/carrier bridge are recorded in the two source packets.
Source identity is not a proof that the new cut's generated declarations have
already been connected to the chosen owners, nor an ELF/runtime theorem.

The NUC Pair-to-Candidate scalar callback/fold and scalar-factor Result maps
have passed against the actual-reader-backed adapter cohort. The full body
map remains open: prefix, high-term construction, and post-term branch/array
transport are now assigned separately for parallel completion. No conditional
tail-map premise is counted as discharged. Whole-loop/caller integration,
release binding, coherent replay and 100-bit composition remain open.


PROVED same-run iterator preservation: actual Pair afterLow, activeBody and
generated source body successful executions return Continue with exactly the
iterator obtained from their range-next step. No canonicality, arithmetic
success or independent tail execution premise is added. Two focused targets
passed (19.198 s and 16.156 s, below 3.23 GB process RSS, zero swaps); all
three theorem reports use only standard axioms. Evidence:
evidence/s9-pair-flowproofs-v1-20261022/.

The scalar-factor Result transport is committed at 2adb24fdf8. The active
prefix map through all eleven child calls has passed on the NUC with an
explicit universal afterLow-map premise; this conditional result does not
close S9. Work is joining the four-term prefix and exact source suffix,
retaining the same bound PERM[3] value instead of positing an independent
second read. Full-loop/refinement/release and 100-bit composition remain open.


PROVED complete Pair-to-Candidate active body transport: the former
universal afterLow equality premise is discharged by the exact source
term-prefix and bound-index suffix maps. Both branches retain the same
PERM[3] value, and the body Result equality preserves failure/divergence
as well as success. Commits 28fe8a9ca3, 4fc322cd33, 42ee84b961; evidence
s9-pair-term-prefix-map-v1-20261022/, s9-pair-afterlow-map-v1-20261022/,
s9-pair-full-active-map-v1-20261022/. Focused full-active check: 19.588 s,
3.19 GB process RSS, zero swaps, standard axioms.

PROVED successful selected helper-loop execution has exactly the two source
active calls followed by its terminal call, reusing the accepted fixed
iterator transitions rather than reproving their arithmetic. Commit
8567e9e6f2; evidence/s9-pair-two-body-calls-v1-20261022/. Focused check:
18.809 s, below 3.16 GB, zero swaps, standard axioms. Complete loop/public
helper transport and genuine actual-core type-to-operation correspondence
are being joined next. Production Rust refinement, release binding and the
composed 100-bit theorem remain OPEN; no S9 release closure is claimed.


PROVED public selected caller helper semantics: the two source helper
iterations and zero-array wrapper transport successful results to the checked
Candidate helper (87f7f8643d). Reusing CandidateTopTotal then proves canonical
returned cells and all original S2 coefficient equations (865ad6a8fb). The
canonical mapped-input-read contracts and successful Pair call remain explicit;
there is no remaining universal afterLow equality or output-canonicality
premise. Evidence: s9-pair-helper-loop-wrapper-map-v1-20261022/ and
s9-pair-public-top-result-v1-20261022/. Checks: 18.914 s, 17.023 s, 18.796 s;
below 3.24 GB process RSS, zero swaps, standard axioms.

This closes the selected helper's internal mathematical connection, not S9's
release cone. Ongoing: actual core-extraction carrier/body correspondence,
actual four-step projection accumulation and its caller contracts, then the
remaining production/refinement/release joins and composed security result.
Production code and measured CU artifacts have not changed in these proofs.


PROVED actual-core carrier/decoder joins: attempt7's generated field type
carriers map injectively to the owned reader types (3f0f8503ad); the literal
transparent from_limbs body maps on the same input array (a83d55ed44), and
from_le_bytes maps on the same input slice (40ffdb8bfc). Sources, body spans,
Rust/tool hashes and focused receipts are retained in the corresponding
evidence/s9-actual-* packets. These results do not discharge the six opaque
arithmetic call boundaries.

Important source-binding refinement discovered in the genuine addition cut:
the retained checked arithmetic extraction forced release overflow checks,
whereas the adopted candidate SBF receipt has no aspis-core overflow-check
override. The no-override addition cut therefore emits wrapping M31.add,
which cannot be equated to checked addition for unrestricted inputs from
Rust source hashes alone. The required next bridge is guarded by canonical
inputs and proved primitive bounds; a forced-checked extraction is diagnostic,
not production-MIR correspondence. There is no arithmetic source closure
claim yet, and production source/ELF/CU artifacts remain unchanged.


PROVED selected projection execution: the helper output's actual coefficient
reads are canonical (598a6aa6b3); a strengthened source body theorem fixes
each iterator index (bd368492e6); the successful four-step source loop yields
its four ordered body executions (ecd9e651ab), and those yield a canonical
cell-4 result and the exact left-associated four-product accumulation
(3cd103587c). The parent S2 projection call composes the same helper and loop
executions (51ded24151), with initial accumulator and helper input canonical
read contracts still explicit. The reached-helper proof was re-pinned to
the owned-reader-backed Funs cohort before this composition. These checks
are focused selected-source results, not a production caller/ELF theorem.

The actual attempt7 field reader also now has a complete Result map to the
owned field reader at the same buffer/index, with no added bound or success
premise (focused target S9ActualWeightsFieldOwnedMapV1, 11.892 s, 2.24 GB,
zero swaps, standard axioms; packet being assembled). Arithmetic addition
extraction has five transparent declarations and compiled no-option owners.
Its canonical-input map to checked arithmetic is in progress, reusing
existing small-word bounds while avoiding a cold legacy proof rebuild.
The overall S9 release cone and 100-bit composition are still OPEN.


## Canonical bridge across the overflow-profile difference

PROVED in `evidence/s9-wide-add-m31-canonical-map-v1-20261022/`
(commit `653f85fb9a`): for two canonical U32 field words, the actual
no-override extracted wrapping M31.add and the retained checked M31.add both
succeed with the identical stored word. The proof establishes intermediate
bounds and the modulo formula; it does not assume successful addition.
This replaces the invalid unrestricted source-hash-based equivalence claim.
Focused check: 17.568 seconds, below 3.22 GB RSS, zero swaps, standard axioms.
The normalized genuine source Types and Funs owners were checked separately.

The two-, four- and eight-component lifts are proved and committed
(`aa5d3e1529`, `289d886919`). The installed-helper connection and output
canonicality also passed (S9WideAddConcreteMapV1, focused check 19.087 seconds,
less than 3.20 GB process RSS, zero swap, standard axioms). It uses the same
actual-source output witness; no independent successful operation is assumed. A fresh narrow source
Charon extraction of WideExact.mul_m31 and its complete reachable scalar-arithmetic
cone has succeeded on the NUC. The first Aeneas translation exited zero but
emitted empty namespaces and is rejected; a nonempty translation is still
required. Extraction alone does not prove its arithmetic map. Actual compiler flags for the deployed SBF artifact remain unpinned;
these source-body results do not close production MIR/runtime correspondence.

The actual reader proof's original small import cohort is valid but its
generated global discriminant instance clashes with the finish model. A
collision-safe explicit instance and dependent reader proofs are being
re-pinned together on the NUC before joint caller use. No historical object
is silently being relabelled as the new cohort.


## Joint reader and actual operation continuation

PROVED `528ea91ef7`: the collision-safe actual-carrier/Owned/Pair reader
cohort checked together on the NUC. Its final full-Result theorem maps the
actual selected reader to the selected Pair reader on the same buffer/index;
the same successful read yields Pair/P6 canonicality. No new index bound or
successful-read premise is added to the Result map. This does not derive
canonicality of `ap0`, `ap1` or `w.extra` merely from projection success: the
selected projection receives those values as arguments. Their upstream read
provenance is still an explicit caller boundary. Thirteen focused stages were
checked in the selected cohort, not the final global release closure.

PROVED `ade422bbf7` and `b0f017d994`: genuine wrapping wide addition on
canonical operands agrees with the installed helper operation, returns a
canonical value, and its decoded value is exactly the field sum. The same
output witness is used throughout. These results reuse CurrentWide's existing
semantic laws; they are source-body joins, not new field algebra.

The scalar-multiplication extraction issue was resolved by an explicitly
labelled top-level reachability shim. Attempt16 emits the real unchanged
WideExact.mul_m31 method and the complete scalar arithmetic cone, including
M31.mul and reduce_u64; the shim itself is not the proof target. Normalized
Types and Funs compiled independently (11.990 and 14.810 seconds, less than
2.24 GB RSS, zero swap). Their source-body arithmetic map is still pending.
Existing R22 wrapping multiplication/reducer results were located for reuse;
no duplicate overflow-bound proof is intended. The next independent genuine
source cut targets QM31.mul. Production artifact correspondence and the
implementation-linked 100-bit target remain not yet established.


PROVED actual reducer and base multiplication: `ac71dde588` checks the full
source-shaped two-fold reducer against R22 for arbitrary U64 words, including
the final guard/subtraction; `051ab5aec5` identifies the genuine extracted
M31.mul output with R22.wrappingMul for arbitrary U32 operands. Existing R22
modular arithmetic/totality is reused. `86f9ffe1b0` connects the independent
QM31 extraction's primitive bodies to the same scalar source and canonical
add/sub proofs. `1b3470afca` aligns the actual CM cross term and complete
emitted operation graph. The complete CM/QM/Wide products and full scalar
source-to-helper result transport are the next consumers, still open.

The WideExact product's full reachable field-arithmetic source cone is now
retained in `eb7cf417ad`. This is nonempty extraction evidence, not its
semantic proof. No shipped Rust, protocol parameters, proof size, or CU
artifact changed during these checks. Final runtime/artifact refinement and
the composed 100-bit per-attempt soundness result remain open.


## Genuine scalar and QM product totality

PROVED `8291f4020e`: the actual extracted WideExact.mul_m31 call succeeds
on a canonical wide input, returns a canonical value, and decodes to the
exact scalar product. The scalar may be any stored U32 word. The proof uses
the existing S3 powers totality owner and the new complete source-to-current
Result maps; it does not assume that the source call succeeds.

PROVED `a8f9e36942`: the genuine QM31.mul extraction maps unconditionally
to R22's wrapping product. On canonical inputs it agrees with the retained
checked product, and same-call success and canonical output are derived.
Three focused checks passed (12.622, 12.714 and 16.298 seconds), below 2.25 GB
process RSS, zero swaps, standard axioms only. The packet retains failed
drafts separately from accepted evidence. Existing R22 arithmetic is reused.

The scalar and QM connections to the installed helper are still being
checked. Full WideExact product, square and mixed-product source bridges,
upstream operand provenance, production compiler/artifact refinement, and
final security composition remain open. These proofs do not close S9 or
establish the overall 100-bit claim. No production source or CU artifact
changed in this continuation.


## Continued source joins — 23 October

PROVED `a5497d8661`: actual QM31.mul, mapped through CurrentWide, equals
the installed helper qmMul as a complete Result on canonical inputs. This
discharges the operation-dispatch seam left by the checked arithmetic proof;
it does not assume a successful actual call. The accepted focused v5 check
exited 0 in 21.745 seconds, process peak 3,199,254,528 bytes, zero swaps,
standard axioms only. Earlier failed drafts are not accepted proofs.
The same commit records actual Wide source mul_by_r/mul_u carrier maps to
the genuine QM extraction's corresponding operations/formula, preserving
failure and divergence (13.508 seconds, zero swaps, standard axioms).

The genuine square/mixed source extraction is retained in `e5ee3804e4`;
its normalized Types and Funs owners passed independently and are retained
in `07d3128c57`. These compile-only owners are not semantic proofs. Full
Wide product, canonical square and mixed-product semantic joins remain
in progress. Production source hashes for field.rs, wide_exact.rs and
weights.rs still match the extraction pins. No production code changed.
The release cone, runtime/artifact correspondence and 100-bit target remain
open. All four session slots resumed active work after an avoidable idle
handoff; root owns the serial local compile/integration queue.


## Square and product source composition continuation

PROVED `14237698a4`: the genuine combined-cut CM31.square call succeeds
on canonical coordinates and its mapped Result is the selected checked square.
Its proof reuses the existing square operand/reducer semantics. PROVED
`e0dc3bc83a`: checked Probe arithmetic maps to the selected checked CM carrier
for add/sub/mul/by-r/double, preserving the full Result. These checked-to-checked
maps do not remove canonicality at the wrapping-to-checked boundary.

PROVED `439786f092`: the combined-cut QM31.mul maps through all nine actual
source calls to the genuine QM multiplication cut, preserving failure and
divergence. A deterministic symbolic generator emits the named component
transport applications and distinct scoped source/target binders; --check
reproduces the kernel-checked source. The same packet contains a generic
reached-success bind lemma; it does not itself supply concrete canonicality.
PROVED `bd27377a5f`: the separate full Wide multiplication extraction's
QM multiplication body maps to that same actual QM arithmetic cut.

Two earlier QM transport attempts hit the local Lean internal memory cap.
They were not rerun with more memory: an explicit map-function-head equality
prevented accidental reduction of the applied generated arithmetic body.
The replacement isolated subtraction proof passed in 11.578 seconds below
2.25 GB, zero swaps, standard axioms. Prior failures remain diagnostics.

Outer QM square, actual WideExact.mul_qm31, full WideExact.mul canonical
semantics and the complete source/caller/release joins remain in progress.
S9 and the overall 100-bit target are still OPEN. No production source or
CU artifact changed in these proof checks.


## Complete square and mixed source bodies — 23 October continuation

PROVED `0b0fe6ecc8`: the combined source QM31.square preserves its complete
Result into the selected checked square on canonical inputs. The proof follows
the actual six-call sequence and derives intermediate canonicality from success
of those same calls. The accepted v11 check took 14.453 seconds, aggregate peak
2,538,930,176 bytes, zero swaps, six standard-axiom reports. Earlier memory-cap
failures were replaced by named suffix proofs and an explicit mapper-head bridge,
not rerun with larger caps.

PROVED `f5dbde8cc1`: the CurrentWide four-remainder canonicalizer is total
and returns canonical coordinates for every stored QM input. The same commit
contains reusable full-Result success reflection, which recovers a successful
source output from the success of its mapped result without a separate
source-success premise.

PROVED source-only packet `s9-combined-wide-mixed-to-current-v1-20261023`:
the actual combined-cut WideExact.mul_qm31 body maps as a full Result into
CurrentWide, with canonical self and arbitrary stored right operand. This includes
the same canonicalizer and two QM multiplications. The focused check took
23.907 seconds, aggregate peak 3,233,185,792 bytes, zero swaps, standard axioms.

PROVED focused mixed-product helper join (19.733 seconds, zero swaps): the
combined source body maps to installed concrete FieldOps.wideMulQM31.
This is a source-to-helper relation, not surrounding caller refinement.

PROVED focused square helper join (8.481 seconds, zero swaps): the actual
source square maps to installed actualQMSquare under canonical input.

PROVED source square total/exact consumer in `f5e50a17c0`: no independent
source-success premise, canonical output and exact square decode. The focused
check took 15.275 seconds, zero swaps, standard axioms. PROVED source mixed
total/exact consumer (17.030 seconds, zero swaps, standard axioms): arbitrary
right input is normalized by the same four-remainder call; the recovered source
output is canonical and has the corresponding exact componentwise product decode.

Still OPEN: full WideExact.mul
canonical source composition, the actual surrounding caller and input provenance,
production adoption/refinement and runtime/artifact correspondence. The full
100-bit release claim remains OPEN. Production Rust and CU artifacts are unchanged.


## Full source arithmetic and actual call boundaries

PROVED source full WideExact.mul totality/exact semantics in focused packet
`s9-source-wide-mul-total-exact-v1-20261023` (17.435 seconds, aggregate peak
3,222,290,432 bytes, zero swaps, standard axioms). The source-to-Current
full Result map covers the exact nine-operation source sequence, using a
canonicality chain derived from those same reached calls. It composes the
existing checked Wide product theorem rather than re-proving field algebra.

PROVED actual frozen Pair-caller square and mixed-product operation maps,
plus the actual generated Pair body's same-run square prefix. The square
prefix derives canonicality from the selected extra read and ties the three
source-cut results to the actual q4/q41/q8/q16 outputs. It does not supply
canonicality of Weights.extra at its upstream producer.

OPEN producer frontier identified concretely: Pair-step extraction receives
Weights and does not contain Weights::new. The actual constructor copies
alpha[8]/alpha[9] into extra; those values originate from semantic transcript
sampling. The constructor/challenge-caller correspondence must be connected
to the existing canonical sampler proofs. Raw proof-buffer field-reader
canonicality alone does not establish this challenge provenance.

Still OPEN in this lane: full Wide multiplication helper/Pair call join,
exact four mixed-product calls through actual afterLow read witnesses,
constructor/challenge and other upstream canonical-input provenance, and the
composed source/caller/release result. No production Rust/CU artifact changed;
S9 and the full 100-bit release claim remain OPEN.


## Installed full multiplication and same-execution term children

PROVED in `s9-wide-mul-pair-helper-bridge-v1-20261023`: the exact source
WideExact.mul full Result maps to the installed concreteFieldOps.wideMul and
the actual Pair caller arithmetic slot on corresponding canonical operands.
The focused check passed in 16.206 seconds, aggregate RSS 3,214,835,712 bytes,
zero swap, standard axioms only. The canonical operand domain remains explicit.

PROVED in `s9-pair-term-children-v1-20261023`: success of an actual Pair term
exposes that execution's PERM/ap1/high reads, mixed multiplication and quarter
scaling successes. This supplies child-call witnesses rather than assuming
independent executions succeed. Focused check: 22.232 seconds, aggregate RSS
3,239,313,408 bytes, zero swap, standard axioms only.

OPEN: use those child witnesses to connect all actual mixed-product reads;
connect the actual full-width tail calls; establish upstream challenge and
constructor provenance; compose the source/caller/release result. The actual
Weights::new extraction reaches an unsupported raw-pointer field write in
Aeneas. A separately extracted pure extra projection is only a candidate and
does not discharge the actual constructor. Semantic sampler/caller links are
being proved independently. Production Rust and CU artifacts are unchanged.
S9 and the 100-bit release target remain not yet established.


## Same-execution four-term and sampler links

PROVED: `s9-pair-prefix-four-calls-v1-20261023` exposes all four actual
term-prefix calls with exact reads, mixed products, quarter products and term
output identities. `s9-pair-four-mixed-reflections-v1-20261023` connects each
observed mixed product to its source-cut successful result. The canonical
mapped-ap1 read contract remains an explicit premise; no fresh arithmetic
call-success or canonical coefficient premise was added.

PROVED: `s9-semantic-validated-canonical-v1-20261023` reflects the sampler
success in the same extracted semantic_validated call and derives canonicality
from the already-proved universal byte sampler. The digest block is arbitrary.
This local method theorem does not supply current semantic_rounds or the
unsafe Weights::new constructor correspondence.

PROVED: `s9-pair-sidezero-mul-call-v1-20261023` exposes the actual side-zero
continuation's three additions and full multiplication success.
`s9-pair-wide-mul-same-call-v1-20261023` derives the raw source multiplication
success from an observed Pair multiplication on corresponding canonical
operands. Canonicality of the actual low/sum operands is being connected.

All these focused checks passed with standard axioms and zero swap. No whole
manifest replay, production Rust change or new CU benchmark was run. S9 and
the full 100-bit soundness target remain OPEN.


## Implementation frontier: adapter versus enclosing shipped Pair

PROVED operation-level source semantics now cover the full Wide multiplication
from a successful Pair-adapter call, including the exact source result, canonical
actual mapped output and field-product decode. The mixed-operation proof also
retains the internal normalized coefficient, its canonicality and exact decoded
product. Three-add accumulation and generic nested-mapped array-update
canonicality are checked; the side-zero and side-one adapter compositions use
the actual same-execution child-call witnesses rather than fresh successes.

Important scope correction: the generated Pair adapter is not yet proved to
refine the enclosing shipped Weights::pair. The earlier extraction manifest
explicitly marks its normalized caller candidate source_equivalent=false.
The green adapter helper/projection decompositions do not remove that gap.
In these packets, references to an actual Pair call mean the concrete call
in the generated adapter, not an established whole-method Rust refinement.

The current shipped Pair method and factored helper bodies were isolated
without synthetic projection shims. Charon succeeded; Aeneas rejected outer
breaks/returns in nested fallible loops. A guard-only candidate did not fix
this. Isolating the fallible loops into small helpers is under feasibility
test; it is not adopted source, and equivalence, artifact identity and CU
impact are unestablished. Explicit field/parser/helper stub environments in
the diagnostic cut remain correspondence obligations.

Still OPEN: enclosing shipped Pair correspondence, sampler caller/constructor
provenance, remaining input contracts and final source/release composition.
No production Rust change, new CU measurement or full release replay has
been performed here. S9 and the 100-bit soundness target remain unestablished.


## Current focused continuation, 2026-10-23

PROVED: the side-zero body and side-one body adapter packets now establish
canonicality of every successful mapped read from their output arrays. Each
uses the same execution's arithmetic and updates. The side-one result derives
its low-input canonicality from the body prefix. All three packet checks passed;
these are adapter results, not enclosing shipped Pair correspondence.

CANDIDATE: the factored source caller now translates with the actual field,
wide field, parser, twofold, grouped helper and accumulator source. The remaining
explicit canonical Q.raw boundary is being connected to existing body-pinned
proof owners. The selected path's tensor method is being incorporated; no
unreachable placeholder is being treated as a proved native implementation.
The Rust refactor remains isolated, with artifact identity and CU gates open.

CANDIDATE: a fully initialized Box::new constructor extraction avoids the
unsupported raw-pointer writes and has no external templates after replacing
one fixed two-element iterator with its ordered writes. Types compiled; Funs
and the same-execution extra-field theorem are being checked separately. This
candidate changes allocation-failure behavior and is not adopted native source.

The two-body adapter composition is being checked after correcting an earlier
failed draft. No result from that failed check is counted as proved.


PROVED continuation: `s9-pair-two-body-canonical-states-v1-20261023`
connects one generated helper execution to both observed body calls, starting
from its own zero initialization. The intermediate and final arrays satisfy
the full mapped-read canonicality contract; upstream ap0/ap1/extra contracts
remain explicit. Focused check: 24.064 s, 3,265,363,968 bytes peak aggregate
RSS, zero swap, standard axioms only. This closes the adapter two-body
canonicality composition, not enclosing shipped Rust source correspondence.

PROVED candidate-only continuation:
`s9-candidate-constructor-extra-exact-v1-20261023` derives the exact alpha[8]
and alpha[9] reads from one successful initialized Box::new constructor
execution and identifies the returned extra array. Focused check: 13.570 s,
2,186,166,272 bytes peak aggregate RSS, zero swap, standard axioms only.
The candidate generated Types and Funs also compiled independently. The
native allocator, alpha provenance, SBF feasibility and adoption gaps remain.
