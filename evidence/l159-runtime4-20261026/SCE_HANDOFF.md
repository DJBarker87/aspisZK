# SCE handoff: shared bytes and annotation proved; L159 remains open

**Target not yet established. Budget exhausted:100/100 Lean,0/10 Kani.**
Branch `codex/cx-l159-runtime4-20261026`. All commits local; no push or merge.
Only SCE modules and this evidence directory changed. No other worker prefix,
session A worktree/candidate, shipped source, harness, key or wallet changed.

## Exact before/after and counted result

Actual latest installed root in this checkout is `AspisR1.Rc5_Top.deployed`.
`SCE_BEFORE_Top.lean.txt` and `SCE_AFTER_Top.lean.txt` remain byte-identical to
that actual source. Its original binders still include independent P/runtime
and the L159 `F3T_Runtime.StoredCarrierBinding c D rust P runtime` input:
for every H and returned accepted run, the ENTIRE run must equal the annotated
source execution. L185 is the same family's deployment alias. Neither is removed.

`SCE_ConditionalTop.deployed` is a checked new endpoint with ONE adversary a:

    P := SCE_Experiment.submission a
    runtime := SCE_Experiment.runtime c hashv copy allocator id a
    entry1 := (eval H a.first).output.entry
    entry2 := (eval H (a.second entry1-input saved post final)).output.entry

The second submission remains response-driven. This endpoint retains L159,
raw join, both native successes, game/persistence and every other Rc5 premise.
It is not promoted to `SCE_Top.deployed` or counted as a premise removal.

The explicit quantifier change is
`forall P runtime, R P runtime` to
`forall a, R (submission a) (runtime a)`.
`SCE_Quantifiers.deployed_iff` and `old_use` prove equivalence/application on
pairs in that construction's image, including old uses whose actual pair is
so identified. They do not prove the unrestricted old statement, surjectivity,
or that the old game types already identify every physical deployment with
this image. The image index is not a hidden source-refinement assumption.

`SCE_LEDGER_DELTA.json` and `SCE_validate.py` re-enumerate the Rc5 atomic-family
ledger, preserving quantified guards/dictionaries/witnesses and all eleven
approved game clauses; no structure bundling is counted as discharge:

- Actual83T/33P/0C ->83T/33P/0C; delta0.
- Deduplicated deployment-inclusive89T/46P/0C -> unchanged.
- All retained audit rows89T/48P/0C -> unchanged.
- Discharged actual families:none. Added/reclassified trust items:none.

## What is proved

1. `SCE_Experiment` constructs account execution and its ghost observer from
   the GExq/CPG response-driven account program. Original entry buffer1 is
   physical public; buffer0 after688 Pool bytes is the stored verifier proof.
   `SCE_Projection.stored/input_projection`, `PublicProjection.bytes`,
   `DeploymentProjection.stored` prove their same-H byte association without
   success, byte equality, admission or crypto/source laws as inputs. This
   closes the old residual STORED SUBCLAUSE on the constructed shared domain,
   not the full L159 family.
2. `SCE_NativeFirst/Second`, `NativeAccepted` transfer actual wrapper success
   through the RETAINED extraction/P1/syscall boundaries on these same inputs.
   `PairAccepted.accepted_pair`, `FirstCutBytes`, `SecondCutBytes`, `CarriedCut`
   compose RawJ's SAME cuts with the original submitted buffers/checkpoint.
3. `SCE_Annotation.transport` proves actual extractor failure-mass equality
   under consistent, known replay suffix plus existing commitment-frame reads.
   `ReplayExtractTransport.extract` proves equality for EACH private coin tape.
   `SingleAnnotation`, `SingleTransport`, `InstalledSingleBound`, `SingleExtract`
   and `SingleNumerical` instantiate this for a SINGLE source pair, retaining
   the raw join. None identifies that source pair with the full adaptive account.
4. Rejected account runs have zero extraction failure mass (`RejectedAccount`),
   while failing/diverging/error prefixes retain every attempted query. Actual
   account/observer issued-query and collision-read/mass bounds are instantiated
   with Q0+Q1+1921 and Q0+Q1+2965. They do not prove source-event transport.

## Why full physical equality is still unavailable

The first-only ByteProver returns after a.first. The physical account program
also runs TX1, performs the adaptive second choice, and runs TX2. An allowed
ignored-answer query inside that choice leaves the first submission, selected
second input and complete account outcome identical but grows the physical
log by1 (`AdaptivePadding`). Both adversaries fit one common finite allowance
Q1+1 (`PaddingCommonBudget`). `PaddingConditions` preserves EVERY predicate
on the selected native inputs, including present game/admission conditions.

`PaddingFirstPass.not_both`, `PaddingNative.incompatible` and final
`NoUniformPhysical.impossible` prove that, conditional on any accepted source
account run, uniform literal first-pass equality cannot hold for both those
adversaries. This is not a deployed attack or claimed full crypto fixture.
It shows correcting the independent binders alone does not supply chronology.
There is no `SCE_Physical.run_eq`; `Physical.run_eq_iff/chronological_iff`
expose the exact remaining source-log/acceptance clauses.

Moving the COMPLETE account execution into P is explicitly checked instead
(`CompleteSubmission`): it charges1921 additional queries and then the old
originalWith experiment runs the verifier again. `CompleteChronology` proves
literal equality then requires an empty suffix. `Numeric` proves the charged
start envelope `(1921+34)*B` exceeds2^-100. This compares upper bounds, not
attack success. No work/metric/target reduction or grinding credit is proposed.

Next deliverable: transport the actual interactive account experiment's
accepted event/recovered words into frozen3's charged raw-join-or-collision
experiment, retaining adaptive/rejected query history and the SAME submitted
bytes/cuts, WITHOUT requiring literal source/annotation log equality and
WITHOUT treating all source-wrapper work as free adversary preprocessing.
The existing data-only RuntimePersistence trust item does not supply this.

## Non-vacuity and exact scope

`SCE_JointObserver.joint` simultaneously establishes BOTH runtime admissions,
SDK/std, BOTH successful local native wrappers, approved game fields a-d,
RuntimePersistence, checkpoint version/history, nonempty physical events,
JFx verifier/public submission bytes AND the computed account observer's
returned stored/public bytes. `FixtureBudget.zero` proves both adversarial
choices use zero queries. The Pool688-byte prefix remains deliberately zero.
The local n1/n2 fixture functions do NOT instantiate AeneasExtraction for the
actual crypto source. The observer's source acceptance flag stays computed;
no all-premises cryptographic headline or deployed forgery is fabricated.

## Validation, resources and retained failures

`SCE_VALIDATION.json` records100 actual one-module Lean invocations:76 passed,
24 failed revisions excluded,0 dependency builds,0 Kani. All76 current modules
have matching exact-source passing receipts. Labels were allocated out of
order: identifiers are not a budget counter. No invocation occurred for070;
101 preceded the chronologically last100. No further compile is permitted.

All proof invocations used the unchanged S2W launchers, coherent SInt2 cache,
`lake env lean -j1 -M7000 -DElab.async=false`, a verified6G/8G/swap0/Tasks64
scope, at most one scope and one Lean process at a time. The final50 invocations
shared ONE interactive admitted scope, sequentially; ScopeGroups identifies
the admission and reference cgroup for every grouped receipt. Denials did not
launch Lean. Batch6 waited for three180s-or-longer retries before admission.
Earlier retry timing deviations are retained explicitly in STAGE3; no blanket
claim of exact timing compliance is made.

Every receipt includes command/target, source revision anchor and exact dirty
source snapshot/hash, directly selected object/sidecar hashes, exit/wall/RSS/
swap/cgroup limits and full printed axioms/errors. `SCE_HOST_MANIFEST.json`
pins final own sources/objects and unchanged launchers; the final audit's
selected own dependencies match it. Historical transitive cache provenance is
inherited from SInt2/Rc5; this is not a fresh full frozen-release rebuild.
Prepared source_revision anchors differ from launch HEAD for004,009–014,074
as corrected in stage notes. Batch6 initially launched atb4e60fafd4 while the
stage5 commit completed; later source-only edits are anchored33e58abfab with
exact dirty hashes. Queued configs retainingb4 are prepared-source anchors,
not claims that HEAD never advanced. No historical binary is attributed to a
changed shipped implementation.

Total Lean wall372.415537231s; maximum RSS7168552KiB from EXCLUDED failure049;
all swaps0. Failure049 was replaced symbolically, never rerun unchanged or at
a raised cap. Default-heartbeat failures029 and091 were replaced by symbolic
projection/explicit congruence, not higher limits. Other failures are retained
elaboration/API/name errors. Only passing declarations are evidence; failed
error-recovery sorryAx output is excluded. Current sources contain no sorry,
admit, axiom, native_decide, depth/heartbeat override or shipped-source change.

Final100: targetSCE_NoUniformPhysical.lean, exit0, wall3.870788042s,
peakRSS5484628KiB, swap0, anchor33e58abfab plus exact dirty hash. It imports
all75 other current SCE modules and audits the actual Rc5 root plus principal
new top results. Every new theorem is printed in its focused receipt; only
propext,Classical.choice,Quot.sound (or subsets/none) appear in passing audits.
No package replay or repeated unchanged full regression was run.

No shipped/cfg(kani) source changed, so the three-ELF rebuild trigger did not
fire. Inherited artifact pins, NOT newly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No binaries, objects, tarballs or ELFs are committed. Host scope closed after
final100. Offline receipt/source/cap/axiom/ledger validation and git diff
whitespace validation pass. The100-bit target remains not established.
