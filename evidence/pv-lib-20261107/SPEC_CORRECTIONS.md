# Frozen specification corrections

## SPEC-C2 — approved D981 / thread-26′, session 3

Before (PSPEC_COMMON revision 1, verbatim):

> On the thread path, `step` is literally
> `PV_THR2_SourceStoreInterpreter.step`, from W4 at the input pin, with its
> `PV_THR2_SourceStoreLibrary.interpret`.

After (PSPEC_COMMON revision 2, verbatim):

> On the thread path, `step` extends the pinned OWNER-aware
> `PV_THR2_OwnInitInterpreterBridged.step`, retaining its registration, operator
> and bridged-allocation layers. At ordinary native writer polls selected by
> `PV_THR2_SourceStoreNative.select`, it uses the five documented source-store
> meanings through `PV_THR2_SourceStoreLibrary.interpret` and
> `PV_THR2_SourceStoreInterpreter.step`, preserving intrinsic catch priority.
> Away from those eight sites it is the OWNER-aware step. The compiled
> composition is `PV_LIB_SPEC_ThreadMachine.step`; `away` states agreement
> against the OWNER-aware interpreter, and `writer` states the selected-site
> comparison.

Witness: `PV_LIB_SPEC_RegistrationGap.steps_differ`, focused Lean 49717,
compares the exact f361 storage-live 14320 (local45, body.drop113).
`raw_next` keeps OWNER.next for every environment; `registered_next` advances
it by one under the pinned OWNER-aware interpreter. The source-selected
descriptor is registered by OwnUniformBindings.step / BindingRegister.register.
Pins: W3 41e76d01fdead952101594b8b0f36a7561d180f2; W4
ce2f78097fa7e3cabc7b66fdfb9445c067917831; original freeze 5e397cb3878.

The replacement retains the five writes at eight sites: f9 at f1/487 and
f15/3756; f10 at f1/930; f93 at f15/3447; f167 at f15/3519,3641,4327;
f289 at f207/8248. All reply arms and invalid-decoding adequacy failures remain.
Affected consumers: all thread specifications using COMMON, especially f361
and OwnInit. The slice closure has none of these sites. No row proof consumes
this library. No endpoint premise, source, provider, trust field or metric is
changed. Source/machine and runtime Values adequacy remain named obligations.
FREEZE.json remains the historical revision-1 hash authority; this explicit
correction supersedes only the quoted common clause and revision heading.

## SPEC-C5 — owner-approved session9: callback allocation is at cut92

Before (verbatim, PV_LIB_SPEC_OwnInitFull.AllocationWitness):

> `callback.frame.remaining = PV_THR2_F361.live.body.drop 94`

After (verbatim, PV_LIB_SPEC_OwnInitCut92.AllocationWitness):

> `callback.frame.remaining = PV_THR2_F361.live.body.drop 92`

The replacement retains every other conjunct verbatim. The historical module
is retained. Consumers must use the new name; no historical result is silently
rebound. The pre-issue callback.store.nextActivation now selects the backing
for13923; cut94 is14113, after the allocation returned. Registration113 and
ready129 are unchanged. Checked witness: CallbackCutCheck.actual_allocation,
actual_site, retained_site, backing_after_return (44928). New source_cut and
source_site reuse those facts. No successful trace or full-joint contradiction
follows just from this correction. Source/resource/native adequacy and the
original-entry successful branch remain required; no success/decoder premise
is introduced. No endpoint/T field, implementation or release pin changes.
