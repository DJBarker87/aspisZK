"""Additive final checks. Never infer closure from local probes or import success."""
from pathlib import Path
import json,hashlib,subprocess,sys,re,copy,lzma
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(E/'NGD_validate.py')],check=True)
subprocess.run([sys.executable,str(E/'NGD_source_erasure.py')],check=True)
rows=[json.loads(l)for l in (E/'NGD_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)==173 and len({r['attempt']for r in rows})==173
expected={f'NGD_{k}{i:03}'for k,n in [('K',100),('L',70),('E',3)]for i in range(1,n+1)}
assert {r['attempt']for r in rows}==expected
missing={'NGD_L001','NGD_L034'}
receipts={}
for a in sorted(expected-missing):
 p=E/a/'receipt.json';r=J(p);receipts[a]=r
 assert r['attempt']==a and r['source_revision'] and 'print_axioms'in r
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0
 for name,h in r['source_hashes'].items():assert sha(E/a/'sources'/name)==h,(a,name)
for r in rows:
 if r['attempt']in missing:assert r['exit_status']is None and r['receipt_available']is False
pairs=[];exclusions={5:'compile allocation API',6:'compile reference visibility',35:'actual decoder timeout',38:'variable-offset decoder timeout',63:'full-output observation timeout',100:'invalid-row unwrap panic outside established caller domain'}
for n in range(1,101):
 a=f'NGD_K{n:03}';r=receipts[a]
 graph=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'));src=J(E/(a+'-source-check.json'))
 assert graph['graph_matches_frozen'] and not graph['new_package_tuples'] and not graph['edge_errors']
 assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert src['files']==len(J(E/a/'sources/NGD_SOURCE_PINS.json')) and not src['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and '-Copt-level=3'in r['env']['RUSTFLAGS']
 features={x['name']:x['features']for x in graph['selected_closure']}
 assert features['aspis-r1-cost-probe']==['default','optimized-terminal','private-leaf-salts','program-build']
 assert 'r0'in features['aspis-statement'] and 'pool-v1-kernel'in features['aspis-statement']
 assert '--locked'not in r['native_command']
 text=(E/a/'stdout.log').read_text()
 if n in exclusions:
  assert r['exit_status']!=0
  if n in [35,38,63]:assert 'timed out'in text
  continue
 if r['exit_status']==0:
  assert 'VERIFICATION:- SUCCESSFUL'in text and '[optimized]'in text
  c=receipts[f'NGD_K{n+1:03}'];s=(E/c['attempt']/'stdout.log').read_text()
  assert c['exit_status']==1 and 'VERIFICATION:- FAILED'in s and 'Failed Checks:'in s and 'timed out'not in s
  assert r['source_hashes']==c['source_hashes']
  if n not in [51,53]:assert r['module']==c['module'] and r['native_command']==c['native_command']
  pairs.append([a,c['attempt']])
assert len(pairs)==47
# Same exact KMX implementation in every gate; no private copy substitute.
kmx=R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
assert sha(kmx)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for r in [receipts[p[0]]for p in pairs]:
 for name in ['NGD_wire.rs','NGD_compact.rs']:
  p=E/r['attempt']/'sources/NGD_src/crates/aspis-r1-cost-probe/src'/name
  if p.exists():
   t=p.read_text();assert not re.search(r'\bstatic\s+(?:mut\s+)?\w+\s*:',t)
# Final coherent import, same-driver fixture controls, raw ax2, NFX scan.
assert receipts['NGD_L067']['exit_status']==receipts['NGD_L068']['exit_status']==receipts['NGD_L069']['exit_status']==receipts['NGD_L070']['exit_status']==0
roots=J(E/'NGD_AUDIT_ROOTS.json')['roots'];summary=J(E/'NGD_stage2_audit/SUMMARY.json');assert summary['status']=='PASS'
raw={x['root']:x for c in summary['commands']if c['target'].startswith('proof')for x in c['results']}
assert set(raw)==set(roots) and len(raw)==67
for x in raw.values():assert x['equal']and set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}
fixtures=next(c for c in summary['commands']if c['target']=='fixtures')['results'];assert len(fixtures)==8
assert all(x['equal']and len(x['walked_axioms'])==1 for x in fixtures[:4])
assert all(x['equal']and not x['walked_axioms']for x in fixtures[4:])
scan=[json.loads(l)for l in (E/'NGD_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==12751 and all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
for x in J(E/'NGD_REUSED.json'):assert sha(R/x['path'])==x['sha256']
# Recheck every final top source against its focused success; no later edit.
for m in J(E/'NGD_AUDIT_ROOTS.json')['modules']:
 r=receipts[m['attempt']];source=m['module'].replace('.','/')+'.lean'
 assert r['exit_status']==0 and sha(E/source)==r['source_hashes']['NGD_generated/'+source]
# Mutation controls preserve the slot-only composed ledger conclusion.
def validate_claim(closed,delta):
 assert closed['new_composed_functions']==1 and closed['new_composed_rows']==2 and closed['driver_root_status']=='OPEN'
 assert delta['new_closed_rows']==['TX1:100','TX2:066'] and delta['new_count']==2 and delta['checks_added_only']
 assert all(x['status']=='OPEN'for x in J(E/'NGD_EDGES.json'))
closed=J(E/'NGD_CLOSED.json');delta=J(E/'NGD_LEDGER_DELTA.json');validate_claim(closed,delta)
for field,bad in [('new_composed_functions',2),('new_composed_rows',3),('driver_root_status','CLOSED')]:
 c=copy.deepcopy(closed);c[field]=bad
 try:validate_claim(c,delta)
 except AssertionError:pass
 else:raise AssertionError('Accepted inflated closure '+field)
assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*')if p.is_file())
out=dict(status='PASS',charged_budget=dict(kani=100,lean_support=70,extraction=3),receipts=171,non_success_without_receipt=sorted(missing),native_pass_control_pairs=pairs,excluded_native=exclusions,composed_functions=1,composed_rows=2,raw_roots=67,fixture_controls=8,scanned_modules=len(scan),mutations_rejected=['inflated functions','inflated rows','headline falsely closed'],quarantined_function_pointer_harnesses=[],suspended_writable_static_harnesses=[],no_cold_release_replay=True)
(E/'NGD_CAMPAIGN_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 173 charged attempts, 47 native/control pairs, 67 raw roots, 12751 modules; only two slot rows CLOSED')
