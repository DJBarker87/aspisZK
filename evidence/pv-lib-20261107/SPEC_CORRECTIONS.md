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

Propagation: `PV_LIB_SPEC_OwnInitCut92Contract.Post`/`Contract` replace the
witness name inside the complete own-row statement; `PV_LIB_SPEC_Cut92Composition`
replaces the OwnInit conjunct and the allocation-branch witness in the full
18-contract conjunction and its existential Witness target. These are compiled
statements, not inhabitants. Other row/domain/runtime clauses are retained.
They do not silently equate the historical Runtime with the sparse/v2 runtime.
The latter's source adequacy is blocked by checked SPEC-C6 in FINDINGS.md.

## SPEC-C6 — owner-approved D993/session10: allocation images per source type/site

Before (verbatim, SparseRuntime.native allocation adapter):

> `PV_LIB_SPEC_SparsePacketHandler.handler C K p.resources p.encode`

After (verbatim, SiteRuntime.native allocation adapter):

> `PV_LIB_SPEC_SiteArc.handler C K p.resources p.encode`

Historical definitions are retained. This new adapter selects the actual
ScopeData or Packet DATA operand's source type tag at the shared4963 token;
the generic F124 body's own ArcInner tag is insufficient. ScopeData is40/8
(qwords0/8/16/24 and byte32, holes33..39); Packet remains48/8 (qwords0/8/16/24,
holes32..47). Source wrapper fields and physical pointer registration are
checked by partial codecs; malformed source representations remain explicit
None. No successful decoder, arbitrary image or return-success premise enters
a MachineSpec. Failures, null/abort and pending retain the named allocation
model for the selected layout before any successful-value decoding.

Checked source-error witnesses are ScopeAllocationGap, ScopeAllocationPollGap
and ScopeRuntimeGap (44960/44962/44965). New SiteArc.layout_distinct,
scope_classified/packet_classified and returned_owned (44974), SiteArcRecheck
scope_handler/packet_reply (44980), SiteRuntime (44977) and SiteV2Runtime
(44981) are the replacement operational facts. SiteHistory.original (44982)
rechecks issued-source origins against that actual v2 execution, not successful
reachability. InitImageRecheck.initPost_memory (44976) rechecks ThreadInit's
existing three-store initializer. AllocationImages (44971) keeps separate
ScopeData, Packet, callback, ThreadInit and thread::Inner store images from
ELF fc8808eb...; SESSION10_ABI_SOURCE.json records full hash, offsets and type
fields. Callback copies preserve source bytes including padding/unknowns.

Affected consumers: the18 historical thread statements and the corrected
cut92 allocation witness retain their old machine definitions and still need
rebinding/adequacy; no old model or full witness is silently relabelled repaired.
The current operational replacement is SiteV2Runtime, using unchanged actual
lane-A v2 in the same W3 cohort. Native Values binding and table completeness
remain open. SPEC-C7 additionally checks that callback image installation is
missing even in SiteRuntime; the separate image definition alone supplies no
source/native binding. Thread::new's separate48/8 image is not Packet's image
and is not silently installed at a native leaf. No endpoint/T field, security
metric, provider or frozen implementation changes.
