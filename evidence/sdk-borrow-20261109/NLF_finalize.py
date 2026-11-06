from pathlib import Path
import json,lzma,re,hashlib,subprocess,collections
E=Path(__file__).resolve().parent
ats=[json.loads(l) for l in (E/'NLF_ATTEMPTS.jsonl').read_text().splitlines()];native=[r for r in ats if r['kind']=='kani'];formal=[r for r in ats if r['kind']!='kani']
outcomes=collections.Counter();classes={}
for r in native:
 s=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 status='NATIVE_PASS' if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s else 'MATCHED_FAILING_CONTROL' if 'Checking harness '+r['module'] in s and 'VERIFICATION:- FAILED' in s else 'COMPILE_OR_CODEGEN_REJECTION_NO_CREDIT'
 outcomes[status]+=1;classes[r['attempt']]=status
assert len(native)==60 and len(formal)==85
assert outcomes==dict(NATIVE_PASS=17,MATCHED_FAILING_CONTROL=19,COMPILE_OR_CODEGEN_REJECTION_NO_CREDIT=24)
rows=[json.loads(l) for l in lzma.decompress((E/'NLF_NLF_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
scan=dict(modules=len(rows),declarations=sum(r['declarations'] for r in rows),references=sum(r['edges']for r in rows),dangling=sum(len(r['dangling'])for r in rows),incompatible_owners=sum(len(r['duplicate_owners'])for r in rows),import_mismatches=sum(not r['imports_match']for r in rows),exit=0,receipt='NLF_L080/receipt.json')
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
raw=[]
for line in lzma.decompress((E/'NLF_L079/stdout.log.xz').read_bytes()).decode().splitlines():
 if line.startswith('NEP_RESULT '):raw.append(json.loads(line[11:]))
assert len(raw)==189 and all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
fixture=json.loads((E/'NLF_NLF_binary_fixtures.json').read_text());proof=json.loads((E/'NLF_NLF_binary_proof0.json').read_text());assert fixture['before']==proof['before']==proof['after']
walker=json.loads((E/'NLF_WALKER_PIN.json').read_text());walker.update(fixtures_receipt='NLF_L070/receipt.json',raw_receipt='NLF_L079/receipt.json',scan_receipt='NLF_L080/receipt.json',same_compiled_fixture_and_raw_binary=True,proof_binary_sha256=proof['before']);(E/'NLF_WALKER_PIN.json').write_text(json.dumps(walker,indent=1)+'\n')
export=json.loads((E/'NLF_EXPORT.json').read_text());host=json.loads((E/'NLF_HOST_FINAL.json').read_text());seed=json.loads((E/'NLF_SEED.json').read_text())
rt=['shared-data','exclusive-data','shared-lamports','exclusive-lamports','try-data-len','data-len','try-lamports','lamports','keys-owner','data-field']
audit=dict(status='SDK_SUPPORT_PACKET_VALIDATED_UNDER_BE2_AU',target_established=False,ledger_rows_promoted=0,ledger20_baseline=dict(closed=560,qualified=0,open=39,total=599),branch='codex/cx-sdk-borrow-20261107',frozen_verifier_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_pool_revision='b936275465',headline='AspisR1.RPx_Deployed.deployed',budget=dict(kani=dict(used=60,limit=60),lean=dict(used=sum(r['kind']=='lean'for r in formal),limit=90),formal_scopes=dict(used=len(formal),conservative_combined_ceiling=90,lean_compilations=sum(r['kind']=='lean'for r in formal),other_scopes=sum(r['kind']!='lean'for r in formal)),extraction=dict(used=0,limit=0)),native_outcomes=dict(outcomes),native_classification=classes,raw_axioms=dict(roots=189,standard_only=True,accepted=['propext','Classical.choice','Quot.sound'],receipt='NLF_L079/receipt.json',manifest='NLF_AUDIT_ROOTS.json'),fixtures=dict(checks=8,all_equal_to_collectAxioms=True,same_compiled_binary_as_final_raw=True,receipt='NLF_L070/receipt.json'),coherence_scan=scan,statement_reviews=dict(receipts=['NLF_L084/receipt.json','NLF_L085/receipt.json'],purpose='Full elaborated wrapper and consumer statement/hypothesis review',new_declarations=0),combined_audits=2,combined_import='NLF_COMBINED_IMPORT.lean',resource=dict(memory_high='6G',memory_max='8G',memory_swap_max=0,tasks_max=64,lean_M=7000,one_scope_at_a_time=True,peak_rss_kib=max(int(r['peak_rss_kib'])for r in ats),total_scope_wall_seconds=sum(r['wall_seconds']for r in ats),swaps=sum(int(r['swaps'])for r in ats),timeouts=0,memory_kills=0,cap_increases=0,own_bytes=host['own_bytes'],host_free_bytes=host['free_bytes']),native_fidelity=dict(frozen_graph_checks=60,unchanged_post_run_locks=60,offline=True,optimized=True,deployed_feature_graph_per_run=True,canonical_kmx_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',kani_version='0.67.0',ref_refmut_stub_verified_uses=0,record_shape='ScalarReply {value:u64,tag:u8}',record_controls=['NLF_K048','NLF_K049','NLF_K050','NLF_K052','NLF_K053','NLF_K054'],quarantined_Option_fn=[],suspended_writable_static=[]),trust=dict(new_runtime_rows=[],reviewed_transcription_items=['NLF-RT-'+r for r in rt],classification='option-A P6/D188 reclassification, never removal',headline_premises_discharged=[],runtime_cpi_readonly_entry7_used=False,retained=['std RefCell/guard interpretation under (be)(2)/(au)','RuntimeEntrypointAdmission and Pool counterpart, including native relatedness','P6/D188 and physical/source/ELF interpretation','allocator/runtime/cryptographic trust as already scoped']),release_artifacts=dict(rebuilt=False,reason='No shipped source changed; only evidence, new NLF modules and a scratch-only cfg(kani) patch',inherited_default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',inherited_devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',owner_amended_pool='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'),seeds=seed['seeds'],export=export['export'],export_bytes=export['bytes'],selected_closure_objects=host['pinned_objects'],no_push=True,no_key_operations=True,no_session_or_sibling_worktree_edits=True)
(E/'NLF_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
handoff=f'''# NLF SDK borrow law handoff

**Target not yet established.** Reusable (be)(2)/(au) SDK support packet supplied;
no native entry/Pool driver closure and no ledger promotion. Baseline ledger20
remains560 CLOSED /0 QUALIFIED /39 OPEN of599. Branch
codex/cx-sdk-borrow-20261107; commits only, no push.

## Established and precise scope

Import NLF_SdkBorrowLaw. Complete shared/exclusive SDK data and lamport wrapper
Results, selected cell/payload, error mapping, scalar getter Drop/panic,
metadata projection/frame, current Ref/RefMut projection, move/drop and token
consumption laws compile. The complete per-cell ledger excludes NJN-F2's duplicate
writer; globally fresh monotone tokens exclude cross-cell ownership duplication.
Acquisition/deref/release and source-ordered folds preserve ownership, and
admitted_counter_range derives -1 <= flag <= 2^63-1 from runtime admission.

Three-account TX1 snapshots/exclusive-copy and seven-account TX2 sequential
snapshot acquisition/cleanup are parent-state token-event laws. All ten source
occurrences have explicit packets. Every reply/error, SAME cell and payload,
lexical Drop, key/alias identity and zero-counter/liveness premise is retained.
The copy law composes ONE native byte window at arbitrary offset/observer over
1768 arbitrary bytes with canonical KMX induction; it also retains borrow Err
and unequal-length abort prefixes. See NLF_LAWS and NLF_CUTS for exact statements.

Actual pinned SDK wrapper code runs in Kani with safely created typed guards;
no Ref/RefMut-returning function is stub_verified. ScalarReply fidelity controls
all behave as required. This is the approved thin-wrapper transcription over
existing std semantics, NOT universal unsafe RefCell verification or a new
native whole-parent certificate. The native safe-constructor domains and the
universal std interpretation are distinguished in NLF_CORRESPONDENCE.

## Validation and trust

Final combined import loads NKW ledger20 + NJN + AspisR1.RPx_Deployed.deployed.
L079:189 raw roots, standard axioms only. Same compiled proof binary/eight
fixtures pass; L080 NFX-style scan exit0 across{scan['modules']} modules,
{scan['declarations']} declarations/{scan['references']} references:zero dangling,
incompatible owners or import defects. Two combined audits total. This is a
focused cached cohort, not a cold release replay. Full{host['pinned_objects']}
selected object/sidecar pins include the Aeneas library actually resolved.
L084/L085 retain full machine-elaborated wrapper/consumer statements with all
implicit arguments shown. These two review modules declare no new constants
and do not change the audited semantic import or require a third combined audit.

Budget60/60 native attempt IDs:{dict(outcomes)}.
Compile/codegen rejections earn no credit; own queue repair and every failed
step are retained.{audit['budget']['lean']['used']}/90 Lean compilations;85 total non-Kani scopes ({audit['budget']['formal_scopes']['lean_compilations']}
Lean compilations, {audit['budget']['formal_scopes']['other_scopes']} link/audit/inspection scopes),0/0 extraction.
All scoped admissions exit0 AND allowed:true; disk >=40GB before each scope.
Caps6G/8G/swap0/tasks64,Lean-M7000,one scope at a time,optimized/offline Rust.
PeakRSS{audit['resource']['peak_rss_kib']}KiB,scope wall{audit['resource']['total_scope_wall_seconds']:.3f}s,swaps0.
No timeout,memory kill,cap increase,unchanged retired rerun or heavy field gate.
Each receipt records target,argv,source revision/dirty snapshot and hashes,
dependency pins,exit,wall,RSS,swap,limits and printed axioms(native:N/A).

SDK pins:solana-program2.3.0,solana-account-info2.3.0,ProgramError2.2.2;
core source/deployed and Kani compiler versions are separately pinned.
Before EVERY native attempt the resolved frozen lock graph is checked offline;
all60 post-run locks remain byte-identical. Final SDK bytes/source/lock and
both programs' SDK dependency closures match. Frozen Pool's new Cargo.toml is
byte-identical to the old manifest; Pool parent bodies were NOT native targets.

Ten per-wrapper ReviewedTranscription items are option-A P6/D188
RECLASSIFICATIONS,never removals. No new runtime row or headline premise
discharge. Existing std semantics, runtime admission/native relatedness,
allocator and physical/source/ELF trust remain. RuntimeCpiReadonlyEntry7 is
PENDING and unused. Frozen3,L154 parameter,narrowed D188,100-bit PER-ATTEMPT,
privacy and the two-transaction contract are unchanged.

## Reuse and remaining work

Own workspace /home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109;
CARGO_TARGET_DIR there as NLF_target. Seeds copied FIRST NJN1099008bytes,
THEN NKW1365368bytes; individual hashes retained. No shared cache writes.
Final export:{export['export']} ({export['bytes']}bytes).
Prepend that export,NLF_seed and the remaining L078 LEAN_PATH; use the full
NLF_CLOSURE_PINS manifest to reproduce selected objects. Own cache/TMPDIR,
source snapshots and exports retained. Host free{host['free_bytes']}bytes;
own workspace{host['own_bytes']}bytes (<30GB). No key/fund/authority action.

Remaining entry/Pool parent cuts must bind these primitives at SAME native
arguments and related runtime heap, construct owned snapshot Vecs, instantiate
actual child packets and retain ordered effects/abort/cleanup. TX1:094 and
Clock/PDA/authentication/Pool continuation work are not silently assumed.
An allocator/copy/caller abort inside a loan must stop at its acquire/deref
prefix with the guard live; SnapshotFold's completed-scope restoration must NOT
be used as an allocator-success premise or a Drop-after-abort event.
Member-by-member obligations are in NLF_REMAINING; no Lean-only SDK law was
left merely because native allowance was exhausted. Unused formal allowance
is not reported as impossibility or exhaustion.

No shipped source or existing proved module changed. Harnesses are committed
as NLF_native_packets.patch plus exact receipt inputs; patch reverse-dry-run
matches K060 bytes. No ELF rebuild trigger. Verifier pins f8c0ec72…/63ad3e9c…
are inherited; latest owner-amended Pool pin is e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc
at b936275465,not the historical121f… in predecessor reports. No fresh artifact
reproduction is claimed. No sessionA/sibling worktree touched.
'''
(E/'NLF_HANDOFF.md').write_text(handoff)
print('NLF finalized handoff/audit:189 standard raw roots;'+str(scan['modules'])+' coherent modules;60 native/85 non-Kani scopes')
