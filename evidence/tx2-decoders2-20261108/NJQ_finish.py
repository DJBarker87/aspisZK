"""Validate receipts and assemble SUPPORT-ONLY handoff facts; no ledger mutation."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess
E=Path(__file__).resolve().parent;J=lambda n:json.loads((E/n).read_text());H=lambda b:hashlib.sha256(b).hexdigest();W=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
R=lambda a:J(a+'/receipt.json')
text=lambda a:lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
std={'propext','Classical.choice','Quot.sound'}
results=[json.loads(l[11:])for l in text('NJQ_L072').splitlines()if l.startswith('NEP_RESULT ')]
roots=J('NJQ_AUDIT_ROOTS.json')['groups'][0];assert len(results)==len(roots)==89 and {r['root']for r in results}==set(roots)
assert all(r['equal']and set(r['walked_axioms'])==set(r['collect_axioms'])and set(r['walked_axioms'])<=std for r in results)
fixtures=[json.loads(l[11:])for l in text('NJQ_L071').splitlines()if l.startswith('NEP_RESULT ')];assert len(fixtures)==8
for i,row in enumerate(fixtures):
 assert row['equal'] and row['walked_axioms']==row['collect_axioms']
 assert row['walked_axioms']==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]][i]
scan=[json.loads(l)for l in lzma.open(E/'NJQ_NJQ_LOADED_scan.jsonl.xz','rt')];assert all(r['imports_match']and not r['dangling']and not r['duplicate_owners']for r in scan)
assert all(R(f'NJQ_L{n:03}')['exit_status']==0 for n in [68,69,70,71,72,73,74])
W('NJQ_AUDIT.json',dict(status='PASS_SUPPORT_AX2_NFX_COMBINED_NO_ROW_CREDIT',combined_import_attempts=2,full_combined_audits=1,failed_preload_receipt='NJQ_L064',successful_combined_receipt='NJQ_L068',fixture_receipt='NJQ_L071',raw_receipt='NJQ_L072',scan_receipt='NJQ_L073',pin_receipt='NJQ_L074',raw_roots=results,fixtures=fixtures,modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,cached_replicas=sum(len(r['cached_replicas'])for r in scan),standard_axioms=sorted(std),headline='AspisR1.RPx_Deployed.deployed',walker=J('NJQ_WALKER_PINS.json'),binaries=J('NJQ_AUDIT_BINARIES.json'),baseline_objects=J('NJQ_PREDECESSOR_COMPARISON.json'),target_established=False,composed_rows=0))
raw=lzma.decompress((E/'NJQ_L068/stdout.log.xz').read_bytes());(E/'NJQ_ROOT_STATEMENTS.txt.xz').write_bytes(lzma.compress(raw));(E/'NJQ_ROOT_STATEMENTS.txt.sha256').write_text(H(raw)+'\n')
rs=[json.loads(l)for l in(E/'NJQ_ATTEMPTS.jsonl').read_text().splitlines()];assert len({r['attempt']for r in rs})==len(rs)
ks=[r for r in rs if r['attempt'].startswith('NJQ_K')];ls=[r for r in rs if r['attempt'].startswith('NJQ_L')]
assert {r['attempt']for r in ks}=={f'NJQ_K{n:03}'for n in range(1,61)};assert len(ls)<=80
native_runs=[r['attempt']for r in ks if 'Checking harness' in text(r['attempt'])]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rs:
 a=r['attempt'];ad=J(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']==limits,(a,r['limits']);assert str(r['swaps'])=='0'
 env=r.get('env',J(a+'.json')['env'])
 assert env['CARGO_TARGET_DIR'].endswith('/NJQ_target')
for a in native_runs:
 g=J(a+'-graph-check.json');assert g['graph_matches_frozen']and not g['new_package_tuples']and not g['edge_errors']
 lock=J(a+'-lock-check.json');assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert not J(a+'-source-check.json')['errors'];assert J(a+'-isolation.json')['allowed']
 assert R(a)['env']['CARGO_NET_OFFLINE']=='true'
# Checked current sources are included in the combined import; no uncompiled draft.
for f in E.glob('NJQ_*.lean'):
 if f.stem=='NJQ_ScanDriver':continue
 h=H(f.read_bytes());assert any(r['module']==f.stem and r['exit_status']==0 and h in r['source_hashes'].values()for r in ls),f.name
pairs=[(6,7),(10,11),(12,13),(15,16),(19,20),(21,22),(23,24),(25,26),(27,28),(31,32),(33,34),(35,36),(40,52),(42,53),(44,54),(48,49),(50,51),(57,58)]
for a,b in pairs:
 assert R(f'NJQ_K{a:03}')['exit_status']==0 and R(f'NJQ_K{b:03}')['exit_status']==1
 s=text(f'NJQ_K{b:03}');assert 'CBMC timed out'not in s and ('Failed Checks:'in s or 'VERIFICATION:- FAILED'in s)
for n in [47,56,60]:assert R(f'NJQ_K{n:03}')['exit_status']==1 and 'CBMC timed out'not in text(f'NJQ_K{n:03}')
assert R('NJQ_K039')['exit_status']==0
basis=J('NJQ_K022-graph-check.json');features=J('NJQ_ALL_CRATE_FEATURES.json');feature_rows=[]
for a in native_runs:
 g=J(a+'-graph-check.json');assert g['graph_sha256']==basis['graph_sha256']
 if 'all_features'in g:assert g['all_features']==basis.get('all_features',g['all_features'])
 feature_rows.append(dict(attempt=a,graph_sha256=g['graph_sha256'],same_complete_metadata_as_K022=True,all_crate_features_embedded='all_features'in g))
W('NJQ_FEATURE_RECONCILIATION.json',dict(basis='NJQ_K022-graph-check.json',all_features_sha256=H(json.dumps(features,sort_keys=True).encode()),method='Exact complete cargo-metadata stdout SHA equality, plus directly retained all_features for later gates; no rerun.',rows=feature_rows))
W('NJQ_RESOURCE_INDEX.json',dict(budget=dict(Kani=60,Lean=80,extraction=1),charged_native_attempts=len(ks),actual_Kani_harness_launches=len(native_runs),formal_support_receipts=len(ls),highest_formal_slot=max(int(r['attempt'][-3:])for r in ls),prelaunch_formal_slot='NJQ_L057 blocked by direct-import guard, no scope launched',extraction_runs=1,native_nonlaunches=[r['attempt']for r in ks if r['attempt']not in native_runs],receipts=[{k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']if k in r}|dict(CARGO_TARGET_DIR=r.get('env',J(r['attempt']+'.json')['env'])['CARGO_TARGET_DIR'],full_receipt=r['attempt']+'/receipt.json')for r in rs]))
W('NJQ_FINAL_CHECK.json',dict(status='PASS_SUPPORT_ONLY',native_attempts=len(ks),Kani_harness_launches=len(native_runs),native_pairs_checked=pairs,identity_shape=dict(real_and_weak_contract=39,inverse=47,unimplied_stub=56,modifies=60),frozen_offline_graph_lock_source_isolation=True,all_admissions_exit0_allowed_true=True,caps=limits,all_swaps_zero=True,current_Lean_sources_checked=True,raw_roots=len(results),NFX_modules=len(scan),composed_rows=0,target_established=False))
print(json.dumps(dict(status='PASS_SUPPORT_ONLY',native_attempts=len(ks),native_harnesses=len(native_runs),formal_receipts=len(ls),axiom_roots=len(results),modules=len(scan),composed_rows=0)))
