# D502 / D478 adopted event-retaining headline

Branch: `codex/pv-evh-20261029`. Worktree exactly
`/Users/dominic/ZK/.worktrees/pv-evh`. Base `ae30a1421e`, experimental draft
merge `d21dfe2888`. All new Lean module names begin `PV_EVH_`; the authoritative
namespace is `R1Z.PrivacyR1HeadlineDeployedEvents` in `PV_EVH_Deployed`.

## Before and after

Before, the historical theorem
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` assumes
`RustRealRefinement` of a Result-only Runtime. Failure and divergence erase
event prefixes, so `actual_factors` cannot be installed as that Result decoder
without additional prefix-fibre laws. The theorem is kept byte-for-byte
unchanged, under its existing name; it is now a historical weaker statement.

After, the adopted endpoint observes `Signal × PV_RJ4IDB.Observation A`.
The observation retains ordered events, terminal outcome, requested/delivered
files and stdout, diagnostics, retry counts/rejections, serialized timing,
oracle prefix and retained side channels. The native experiment samples its
native carrier and acquires environment/coins through an explicit map. The
ideal samples the public environment jointly with existing simE coins and
uses the public witness-free completion kernel. The environment law is an
explicit JOINT `EqualLaws` link, not a tautological identity or separate clock
and signal marginals. All Boolean event decisions and adaptive programs remain
quantified; no successful-return restriction is added.

The bound is token-identical to the experimental draft and the historical
headline expression:

```
modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486
  + QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1)
  + 2 * ProverCommitSeedEvent19.budget (2^64)
  + 2 * ProverCommitFuelMass22.charge
```

`simE`, `core_privacy` and `privacy_transport` are reused unchanged. The exact
route adds no trace/timing term and retains the numerical envelope and
`< 2^-100` bound. The separate approximate route is
`PV_EVH_Residual.headline_plus_trace`, with named `deltaTrace` and no automatic
transfer of the numerical target. No native nonzero residual bound is claimed.

Removed from the adopted endpoint: the impossible Result-carrier installation
and its success/failure/divergence prefix-fibre obligations. Removed native
acquisition or joint-simulation obligations: none. The nine original typed
OpenInputs, D163, ordered-event context, D166, V400, signal agreement, causal
prefix and observer-program consistency remain named ordinary Props. The
publication input is reused once; op227 retains V244's existing all-claims
selected-callback equality. The conjunction does not contain the headline or
its probability bound. `LINKS.md` supersedes pv-top's map for this target.

T is unchanged: exactly entropy_law, entropy_kernel, observation. Compiler
preservation V370/D381/D386, V371, rdea-1, E1/E2, native source/provider and
live caller/handle association remain at their previous boundaries. No
own-1, own-2''' or b3p6-1 native credit is claimed. No quarantined Kani result
is used. No crates/programs, frozen ELF pins or keys were changed.

## Satisfiability and fixture non-vacuity

`PV_EVH_Satisfiability` constructs one model runtime;
`PV_EVH_ModelData` closes the external types, operation table, semantic oracle
and point with explicit synthetic values; `PV_EVH_ClosedModel` proves the conjunction
of ALL links simultaneously. It has a nonempty failure prefix, rejected
attempt, oracle bytes, varying environmental clock bytes, their returned/stdout
copies and retained bytes. Its event observer type is unrestricted. Its native
channels are explicit model projections and its op227 reference is the explicit synthetic
operation itself for every claims array, including failure layers. This is
labelled MODEL INSTANCE; it is no deployed source association or native proof.

`PV_EVH_FixtureConsumer` fixes the byte-handle fixture caller statement and a
concrete complete-event adversary carrier, and consumes the exact installed
SDK two-transaction witness from research merge `06f74c902f`. It retains
`FixturePdaRuntime base` explicitly. It must NOT be compiled by this worker:
`AGG16-REQUEST.json` requests the lead's 16 GiB aggregation. The mathematical
public fibre and the two-transaction wrapper witness are distinct from native
trace acquisition, template selection and source/provider association. A
parameterized Runtime alone is not a concrete supplied live producer.

## Validation and AGENTS.md section 6

Per-attempt original output, time data, source revision, source/dependency
fingerprints and complete printed axiom sets are retained in `receipt-*.json`,
`out-*.log`, `time-*.log` and `prepare-*.json`. Final totals follow below. Every host
attempt uses one 6G/8G/swap-zero scope, TasksMax=64, Lean -M7000, admission
exit zero AND allowed:true checked in the launching shell. The failed-source
hash guard refuses proof/elaboration failures unchanged; environment exceptions
require explicit classification and correction evidence. No native scopes,
Kani, extraction or full release replay are authorized or run.

The predecessor cohort is verified before compilation: selected source hashes
under EJR/freeze/h5 precedence, complete project dependency edges, external
manifest hashes, toolchain githash and inherited LEAN_PATH prefix. Reused
objects are read-only. No library or shared project object is rebuilt or
replaced. The new private host directory is
`/home/dombarker/project-offloads/codex-pv-evh-20261029/`.

Privacy target not yet established: the owning lines must supply the native
links in `LINKS.md`; the lead must run the requested fixture consumer. These
are not replaced by the satisfiability model or by source-level checks.

## Concrete deployment limitation

The frozen inputs do not supply a closed live event-producing Runtime: the old
`PV_RunJoin_Deployed.execute` still returns Result, while
`PV_RunJoin_EndpointSelection` still takes selected/public records as data.
The nine open producers and full source/provider association are precisely the
missing native inputs. This work does not fabricate those records or replace
them with model projections. Consequently the adopted headline is a checked
conditional event-runtime theorem; a fully selected live deployed instance
(V045 in particular) is NOT supplied. The consumer concretely fixes the fixture
statement, deployedInstance source calls and adversary carrier, and asks the lead to check its exact same-SDK
execution witness under the retained runtime premise. This is the remaining
part of task (4), separate from the successful interface adoption.

The next concrete deployment deliverable is the runjoin/client event-producing
source selection, with its statement/handle/world association, followed by the
lead's `PV_EVH_FixtureConsumer` aggregation. Native links in LINKS.md stay open;
the full deployed privacy target and a final release closure replay are not
claimed here.

## Rejected attempts and admission evidence

70404 reached elaboration and rejected a malformed application of the public
environment link. The source changed before 70405 passed. 70406 rejected the
local `log` binder because it expanded the protocol notation; it was renamed
before 70407. 70407 then identified an unavailable prefix lemma name; the
replacement supplies an explicit empty extension. 70409 showed that the
projection needed an explicit `change` to expose the constant model trace;
the replacement is symbolic, with no large reduction or resource override.
Every failed source remains recoverable at its recorded source revision and
hash. No rejected theorem or diagnostic sorryAx is consumed as accepted evidence.

Admission refusals are uncharged and preserve the same unused ID after a full
180-second cooldown. The original inherited wrapper overwrote same-ID refusal
receipts; this line preserves each later refusal in an append-only history file.
The first 70407 refusal's full admission record was overwritten by its second
refusal; both refusal events are observed in tool output, and the evidence loss
is recorded in `admission-record-note.json`. This is not a compiler resubmission.
An own-input metadata filename briefly matched the cooldown-receipt glob; it
was renamed before launch. No compiler ran on that error or on a refusal.

## Composition checked

`toCoreLinks` constructs the original fuel-join coupling from D163's two
marginal equations, retaining the original model/seed/fuel coordinates and
adversary-only query suffix. `full_agreement` reconstructs the complete native
trace from ordered context and the joint timing list, then pairs it with the
same option-B signal. Embedded clock bytes in JSON/stdout remain in context.
No error or divergence prefix is discarded. `native_factorization` and
`actual_factors` are reused through the adopted observation interface.

The fixed-environment core applies the existing `core_privacy` and
`privacy_transport` unchanged, for the public completion's pulled-back adaptive
observer. The averaging theorem samples environment/noise jointly with game
coins. The endpoint's PublicEnvironment link then transports the actual native
sample through its acquisition map to that exact public product. Finally the
existing numerical envelope is reused. These are conditional model equalities
and inequalities, not independent marginal arguments about native channels.

## Final focused result

All eight substantive adopted modules pass. The combined statements/axioms
audit **70498** and the single final focused cached replay **70499** pass.
The audit prints the exact adopted theorem and all 18 links, as well as the
closed external-data satisfiability theorem. Every accepted printed axiom set
is a subset of **{propext, Classical.choice, Quot.sound}**. The complete original
lines are in `out-70498.log` and each `receipt-*.json`; rejected diagnostics
are never accepted or imported. No sorry/admit/native_decide/implemented_by,
new axiom, recursion limit or heartbeat override appears in the new source.

Actual Lean attempts: **14/100**, **10 accepted / 4 rejected**. IDs are
70400–70411, 70498 and 70499; 70497 remains unused. Native scopes **0**, Kani
**0**. Four admission refusals occurred before compilation, each followed by
the required cooldown. There were **0 VOID launches**, **0 cooldown violations**
and **0 unchanged failed-source resubmissions**. The rejected sources changed
before their replacements were submitted. The proof-only carrier adoption
removes the Result-fibre installation requirement; unused budget is not
reported as exhausted and does not justify inventing a native association.

Peak RSS across all attempts is **4,279,988 KiB**, swap **0**. Exact per-target
wall time, exit, RSS, swap, source revision, Git blob, source/dependency hashes
and original axiom outputs are recorded in `receipts.md`, `summary.json` and
individual receipts. Guard SHA256 is
`834712a75ce60216319f0ca6c22587412cdb913feb9b9cf69a1b90c43f1d82d6`.
`proof-source-freeze.json` pins every new Lean source, including the uncompiled
lead-only consumer. `final-manifest.json` records the focused accepted closure
and its final read-only source/object/cohort verification: **10 modules,
14 added theorems, 6,376 object hashes, zero mismatches**. The summed Lean
command wall time is **240.46 s**; this excludes admission waits and preflight hashing.

`check.py` confirms the historical Result theorem is byte-identical, the bound
is unchanged, all nine typed inputs are reused, every new docstring is labelled
with D502/D478, the lead-only consumer was never submitted, and each evidence
file is below 20 MB. No crates/programs, soundness-cone file, T field, shared
source/object or release artifact was changed. No key was created or removed.

`COMMITS.txt` records `git log --oneline ae30a1421e..HEAD` before the final
receipt/report commit. No push or merge was performed by this worker.

The full deployed privacy target is **not yet established**. Remaining work is
exactly the native event-producing selection and named links in `LINKS.md`,
plus the lead's explicitly deferred 16 GiB fixture aggregation. The checked
model witness is satisfiability evidence, not a live native execution.
