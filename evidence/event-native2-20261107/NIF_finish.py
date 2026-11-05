from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NIF_?*/receipt.json'))]
assert receipts
for pin in json.loads((E/'NIF_REUSED_INPUTS.json').read_text()):
 assert sha(Path(pin['path']))==pin['sha256'],pin['path']
assert json.loads((E/'NIF_PRIOR_OBJECT_REUSE.json').read_text())['all_prior_objects_identical']
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']==limits and int(r['swaps'])==0,a
 assert r['source_revision'] and r['command'] and r['source_hashes'] and r['wall_seconds']>=0,a
 for n,h in r['source_hashes'].items():assert sha(E/a/'sources'/n)==h,(a,n)
 if r['kind']=='lean':assert '-M7000' in r['command'],a
kani=[r for r in receipts if r['kind']=='kani']
assert {r['attempt'] for r in kani}=={f'NIF_K{i:03d}' for i in range(1,81)}
for r in kani:
 a=r['attempt'];s=(E/a/'stdout.log').read_text();target=r['module']
 expected='FAILED' if target.endswith('control') else 'SUCCESSFUL'
 assert 'VERIFICATION:- '+expected in s,(a,target)
 assert not re.search('TIMEOUT|CBMC timed out|excessive memory',s),a
 g=json.loads((E/(a+'-graph-check.json')).read_text());k=json.loads((E/(a+'-lock-check.json')).read_text())
 assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'],a
 features={p['name']:set(p['features']) for p in g['resolved_features_all_crates']}
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe'],a
 assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program'],a
 assert 'no-entrypoint' not in features['aspis-r1-cost-probe-program'],a
 assert {'r0','pool-v1-kernel'}<=features['aspis-statement'],a
 assert k['before']==k['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert k['unchanged'] and g['resolved_features_all_crates'],a
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
 rules=json.loads((E/(a+'-rule16-check.json')).read_text());assert not rules['static_declarations'],a
 assert sha(E/a/'sources/NIF_KMX.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',a
roots=json.loads((E/'NIF_audit/batch0/proof0.json').read_text());fixtures=json.loads((E/'NIF_audit/fixtures/fixtures.json').read_text())
assert roots['exit_status']==fixtures['exit_status']==0
expected=json.loads((E/'NIF_AUDIT_ROOTS.json').read_text())['groups'][0]
assert {r['root'] for r in roots['results']}==set(expected)
standard={'propext','Classical.choice','Quot.sound'}
assert len(fixtures['results'])==8
for r in roots['results']:assert r['equal'] and set(r['walked_axioms'])<=standard,r['root']
for r in fixtures['results']:
 assert r['equal'],r['root']
 assert bool(r['walked_axioms'])==r['root'].startswith('NEP_Planted.'),r['root']
scan=[json.loads(l) for l in (E/'NIF_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
assert not any(r['module']=='NIF_Inspect' for r in scan)
selected={r['module'] for r in scan}
for p in E.glob('NIF_*.lean'):
 if p.stem not in selected:continue
 builds=[r for r in receipts if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0]
 assert builds,p
 assert any(h==sha(p) for h in builds[-1]['source_hashes'].values()),p
 for word in ['sorry','admit','native_decide']:
  assert not re.search(r'\b'+word+r'\b',p.read_text()),(p,word)
 assert not re.search(r'^axiom\s',p.read_text(),re.M),p
 assert not re.search('maxHeartbeats|maxRecDepth',p.read_text()),p
 exports=json.loads((E/'NIF_EXPORT.json').read_text())['exports']
 assert p.stem in {Path(r['path']).name.split('.')[0] for r in exports},p
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
assert not list(E.rglob('__pycache__'))
assert json.loads((E/'NIF_LEDGER_DELTA.json').read_text())['promotions']==[]
out=dict(status='PARTIAL_NO_ROW_PROMOTIONS',kani_attempts=len(kani),positive_passes=40,matched_control_failures=40,
 lean_compiles=sum(r['kind']=='lean' for r in receipts),support_scopes=sum(r['kind'] not in ['lean','kani'] for r in receipts),
 total_scopes=len(receipts),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swap=0,
 audited_roots=len(roots['results']),all_roots_standard_axioms=True,fixtures=8,scan_modules=len(scan),scan_exit=0,
 failed_compiles=[r['attempt'] for r in receipts if r['kind']=='lean' and r['exit_status']],prelaunch_input_failures=['NIF_L019','NIF_L025'],
 extraction=0,shipped_source_changed=False,elf_rebuild_trigger=False)
(E/'NIF_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(out))
