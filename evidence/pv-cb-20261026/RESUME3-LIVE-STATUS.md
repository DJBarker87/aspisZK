# Resume 3 final status

**Budget exhausted; target not yet established.** Candidate source rows
**18/73 → 23/73**; endpoint premises removed: **0**. The complete73-op table
is [RESUME-SOURCE-ROWS.md](RESUME-SOURCE-ROWS.md). New rows:

|op|row|theorem|source-law receipt|
|---:|---|---|---|
|84|V206|PV_CB_Op84Exact.op84_source|27138|
|105|V211|PV_CB_Op105Exact.op105_source|27105|
|107|V212|PV_CB_Op107Exact.op107_source|27113|
|109|V213|PV_CB_Op109Exact.op109_source|27122|
|118|V218|PV_CB_Op118Exact.op118_source|27127|

Every statement preserves complete Result behavior for arbitrary inputs;
there is no desired-output, canonicality or primitive-totality premise.
Op109 uses the P6 canonicalization leaf completion, including the passing
no-stub native constructor reference gate and extracted safe reference;
all other new rows use complete direct extraction. D188 extraction trust and
P6/native-check trust are retained, not converted into cryptographic axioms.
Older published Source107/109/118/84 files remain byte-identical.

**69/69 Lean compiles used:66 green,3 failed**, IDs27100–27168. Failed27109
needed a logical Option tag instance;27129 needed an explicit native carrier
instance;27163 omitted a function-valued hash binder in generated proof
arguments. Changed-source replacements pass. Failed outputs, including their
error-recovery sorryAx printouts, are rejected and retained as failures.
There were no memory kills. Maximum peak RSS4312096KiB; all swaps0.
[RESUME3-RECEIPTS.md](RESUME3-RECEIPTS.md) links exact target, exit, wall,
RSS, swap, revision, source/dependency hashes and full axioms for every run.
Run revisions are actual launch HEADs; source SHA records the exact dirty
input later committed. Final sources match those receipt hashes.

**Final integrated audit27168** runs in PV_CB_CandidatePublic, the final
projection group: exit0,1.72s,4302668KiB,swap0. It checks64 distinct
declarations:23 published row laws,23 joint projections,18 new
carrier/generic/P6 helpers. Only propext/Classical.choice/Quot.sound or none.
Its two public projections print twice (66 lines). All five groups and the
23-row dictionary are checked. The same audit commands exist in generated
CandidateAudit; its standalone object27135 is the superseded22-row version,
not a final current-source compile claim. Resume3SourceAudit remains an
uncompiled draft; its useful declarations are covered in27168.

One final focused manifest replay checked the older18 source-law modules
and five carrier transports under the restored environment, then rebuilt
the changed dictionary and dependent groups. The final snapshot finds
**zero current direct dependency hash mismatches** for all latest accepted
compiled modules. Unchanged transitive library/candidate objects were
reused; this is not a coherent full frozen-release/privacy-endpoint replay.
See RESUME3-FINAL-FOCUSED-MANIFEST.json and
RESUME3-FINAL-CACHE-DEPENDENCIES.json.

**Kani queue stopped at its first configuration failure.**2/10 runs used:
checks::wide_new_reference PASS; checks::circle_sample_reference compiler
thread-spawn ICE before verification.8 runs remain but were not queued.
No checked shipped-source ROW counterexample. Op259 retains exact
Drop/loop-join extraction obstructions and a prepared safe reference.
Op117 remains PARTIAL: eight changed-property limb gates are prepared and
NOT RUN. No timed-out gate was rerun unchanged. See
RESUME3-KANI-QUEUE-STOP.json and RESUME3-MASK-WORD-SPLIT.json.

No scope or local Lean ran before restoration flag observation/read at
22:02:41UTC. No old ID was reused. Own host directory survived but its
lean-objects cache did not: rebuilt from restored joint objects and populated
with checked outputs. Later external restoration supplied the historical
missing dependencies. Own Lean cache is retained as requested. Own disposable
Rust target caches were removed after the job; pinned tools and evidence are
retained. No wallet/key actions.

Shared PV_CB source/object replacements were snapshotted under own
shared-backup-e9590276cf; all dependents used by the final dictionary were
rebuilt against actual dependency fingerprints. ProverRw interfaces were
copied byte-for-byte only after comparison with the read-only candidate
branch. No shared launcher/infrastructure edit, shipped-code change,
push or merge. Native erasure/fence/Drop/time, filesystem and worker effects
remain deferred to pv-runjoin with exact reasons in the table.

Next deliverable: pv-join can consume the stable source laws and checked
joint23-row dictionary. Op117's full source binding remains open; resume
its smaller gates only after the Kani configuration obstruction is resolved
in a newly authorized run. The unmerged candidate is not the frozen deployed
release; no privacy or side-channel endpoint premise was removed.
