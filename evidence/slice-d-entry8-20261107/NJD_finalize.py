from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(s) for s in (E/'NJD_ATTEMPTS.jsonl').read_text().splitlines()];ks=[r for r in rows if r['attempt'].startswith('NJD_K')];ls=[r for r in rows if r['attempt'].startswith('NJD_L')]
assert len(ks)==24 and len(ls)==33
assert len({r['attempt'] for r in rows})==len(rows)
for r in rows:
 ad=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert int(r['swaps'])==0
 if r['attempt'].startswith('NJD_K'):
  lock=json.loads((E/(r['attempt']+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']
  assert (E/(r['attempt']+'-graph-check.json')).exists()
rootlist=json.loads((E/'NJD_AUDIT_ROOTS.json').read_text())['groups'][0]
mods=['NJD_Trace','NJD_GuardCuts','NJD_EntrySpine','NJD_LaneStep','NJD_DigestLaw','NJD_Prefixes','NJD_COMBINED_IMPORT','NJD_RootStatements','NJD_Inspect','NJD_P7Inspect']
manifest=[]
for m in mods:
 h=sha((E/(m+'.lean')).read_bytes());ok=[r for r in ls if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert ok,m
 manifest.append(dict(module=m,sha256=h,accepted_attempt=ok[-1]['attempt']))
(E/'NJD_SOURCE_MANIFEST.json').write_text(json.dumps(manifest,indent=1)+'\n')
scan=[json.loads(s) for s in lzma.decompress((E/'NJD_NJD_LOADED_scan.jsonl.xz').read_bytes()).decode().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
for n in [27,28,29,30,31,32,33]:assert next(r for r in ls if r['attempt']=='NJD_L%03d'%n)['exit_status']==0
raw=lzma.decompress((E/'NJD_L028/stdout.log.xz').read_bytes()).decode();assert 'sorryAx' not in raw
for r in rootlist:assert "'"+r+"'" in raw,r
native_positive=[2,4,6,8,10,12,14,16,18,21,23];native_negative=[3,5,7,9,11,13,15,17,19,22,24]
for n in native_positive+native_negative:
 a='NJD_K%03d'%n;r=next(r for r in ks if r['attempt']==a);s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==(0 if n in native_positive else 1)
 assert 'VERIFICATION:- '+('SUCCESSFUL' if n in native_positive else 'FAILED') in s
 assert 'Timed out' not in s and 'TIMEOUT' not in s
export=json.loads((E/'NJD_EXPORT.json').read_text())
x=dict(schema_version=1,status='GATES_PASS_NO_NEW_COMPOSED_ROWS',target_established=False,headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',kani_budget=dict(limit=100,used=24,remaining=76,cut_positive=9,cut_matched_controls=9,copy_positive=2,copy_negative=2,diagnostic=2),formal_budget=dict(limit=90,scopes_used=33,remaining=57,lean_compiles=sum(r['kind']=='lean' for r in ls)),extraction_budget=dict(limit=0,used=0),raw_ax2=dict(receipt='NJD_L028',roots=len(rootlist),allowed=['propext','Classical.choice','Quot.sound']),fixtures=dict(receipt='NJD_L027',count=8),NFX=dict(receipt='NJD_L029',loaded_modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,incompatible_owners=0,imports_mismatched=0,cached_compatible_replicas=sum(len(r['cached_replicas']) for r in scan)),combined_import='NJD_L022',statements='NJD_L030',root_hypothesis_inventory='NJD_ROOT_INVENTORY.json',new_composed_rows=0,remaining_rows=17,early_stop_inventory='NJD_REMAINING.md',new_trust_rows=[],composition_trust='Owner option A retained P6/D188 reclassification, never removal',quarantined_NJD_harnesses=[],suspended_writable_static_NJD_harnesses=[],shipped_files_changed=False,ELFs_rebuilt=False,ELF_statement='Inherited release pins only; no shipped source change',scope_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),max_scopes=2,concurrency_note='Initial L002 overlaps K001 under JOB-specific allowance; subsequent scopes serial',scope_wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,no_timeout_or_memory_kill=True,export=export)
(E/'NJD_AUDIT.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NJD_RESULTS.tsv').write_text('attempt\ttarget\texit\twall_seconds\tpeak_rss_kib\tswaps\n'+''.join('\t'.join(str(r[k]) for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps'])+'\n' for r in rows))
# Check every archived input by content, not only its index.
idx=json.loads((E/'NJD_INPUTS.json').read_text())
for h,z in idx['objects'].items():
 p=E/z['path'];assert sha(p.read_bytes())==z['archive_sha256'];assert sha(lzma.decompress(p.read_bytes()))==h
assert not subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs','docs/research/100bit-spend-path-20261013/crates','docs/research/100bit-spend-path-20261013/programs']).strip()
(E/'NJD_FINAL_CHECK.json').write_text(json.dumps(dict(source_receipts_match=True,input_archives_verified=len(idx['objects']),all_57_admissions_allowed_exit0=True,all_native_locks_unchanged=True,all_expected_controls_semantic_fail=True,shipped_source_diff_empty=True,export_retained=True),indent=1)+'\n')
(E/'NJD_HANDOFF.md').write_text(f'''# NJD entry8 handoff

Target not yet established. **No new composed rows; all17 assigned entry occurrences remain OPEN** on NIU ledger13. Branch codex/cx-slice-d-entry8-20261107; no push. Headline AspisR1.RPx_Deployed.deployed; frozen Rust4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Frozen3, L154 parameter, narrowed D188, per-attempt100-bit target, privacy and two transactions retained.

## Established and limited

NJD_INVOCATION.md/JSON inventories239 source-ordered calls in17 occurrences, with expression arguments evaluated before their enclosing calls, deployed cfg filtering, CLOSED law roots and exact unmatched-law categories. Source snippets are pinned once. Digest/error slots are op43/op44; master/checkpoint/lane are op48/op49/op50.

Eight metadata-guard native cut/control pairs and one lane digest-iteration pair ran. Guard native construction has deferred bytes and cannot be promoted to arbitrary full Vec/heap/cleanup. Lane covers every32-byte input and an arbitrary node/level, including assigning the node before a later rejecting empty-root check. NJD_DigestLaw.stub_source discharges its complete canonical/error value law against the CLOSED NFY decoder. Native frontier-element association and op50 whole-body endpoint remain OPEN. NJD_CUTS/STUBS/CERTIFICATES quote exactly what the typed cuts assert; no pointer-to-payload or child-success premise.

NJD_Trace/EntrySpine prove chronological model invocation composition and erasure to NIV's actual emitted entry/process, with complete child Results and retained fail/div call prefixes, no suffix after abort. NJD_Prefixes proves the two TX1 route traces. These are model/source support, **not a native full parent certificate**. No positive entry root satisfying(aq)(2) is claimed; NJD_ROOT_INVENTORY and L030 print the statements and distinguish generic operations/local support hypotheses from permitted physical root hypotheses. Admission1/2 are not silently discharged.

## Gates and receipts

Combined L022 loads NGK+NIU+NIV+NJD with the headline. L027 eight fixtures PASS; L028 raw ax2 all32 roots standard axioms only; NFX L029 exit0 on{len(scan)} modules,{sum(r['declarations'] for r in scan)} declarations,{sum(r['edges'] for r in scan)} references, zero dangling/incompatible owners/import disagreement.1811 compatible replicas disclosed. Library objects are pinned by resolution and closure manifest ({export['selected_objects']} objects/sidecars). Current accepted source hashes and every archived input verify. One combined audit, no unchanged full regression.

Budget:24/100 Kani (9 cut positives+9 matched assertion failures,2 canonical-copy positives+2 matched copy failures,2 diagnostics);33/90 formal scopes ({x['formal_budget']['lean_compiles']} Lean compiles plus links/audits/retention);0/0 extraction. Remaining76 Kani/57 formal. The below80% stopping inventory is member-by-member in NJD_REMAINING.md: OPEN actual children, unavailable exact SDK/P7/PDA/carrier laws, zero extraction authority and observer quarantine prevent complete parent admission. This is incomplete entry closure; no proof count is a status promotion.

Every scope had admission exit0 AND allowed:true and6G high/8G max/swap0/tasks64; Lean-M7000; Rust optimized/offline with frozen graph and unchanged lock before/after every native run. Initial L002 overlapped K001 under the JOB-specific two-scope permission; all subsequent scopes serial. Total scope wall{x['scope_wall_seconds']:.6f}s; peak RSS{x['peak_rss_kib']}KiB; swap0. Exact targets/commands/revisions/source/dependency/axiom pins are in per-attempt receipts and NJD_RESULTS.tsv. No timeout/memory kill/cap increase or unchanged killed/timed-out rerun. Own input/parser/proof repairs are retained in NJD_FAILING_STEP. KMX canonical negative controls fail; no custom copy stub.

## Restore and next work

Host /home/dombarker/project-offloads/codex-cx-slice-d-entry8-20261107; predecessor export seeded FIRST,2262936 object bytes plus2412 metadata bytes, all12 object hashes match. Own retained export {export['path']}, {export['bytes']} bytes, tree{export['tree_sha256']}. Prepend it and NJD_seed to the recorded L033 LEAN_PATH for restoration. Own objects/seed/cache retained; only own Cargo target/native audit rebuildables/solver scratch removed under rule9. CARGO_TARGET_DIR was always the owned NJD_target and is recorded even for non-Cargo scopes. Host initially99% full; NJD_HOST_END records recovered space.

Next deliverable: an ar(2)-licensed complete SDK/primitive/callee law and its full pre/post native parent cut, followed by actual discharge of each child clause under(aq). The concrete missing laws are indexed by member in NJD_REMAINING; TX1 candidate::tx1 TX1:094 and TX2 account decoders remain genuinely OPEN in NIU, not merely re-export naming defects. Do not repeat NIV_K038 or replace any missing law by an endpoint premise. No RuntimeCpiReadonlyEntry7 or XRn kit.

No repository shipped file, existing proof, sibling/sessionA worktree or key was changed. No ELF rebuild trigger. Inherited only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. New trust rows0; P6/D188 option-A transport retained as reclassification.
''')
print(json.dumps(dict(status=x['status'],rows=0,kani=24,formal=33,raw_roots=32,modules=len(scan),inputs_verified=len(idx['objects']))))
