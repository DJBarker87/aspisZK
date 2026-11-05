"""Add checks without weakening any inherited row or admitting local fragments."""
from pathlib import Path
import json,hashlib,lzma,copy,re
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def validate():
 standard={'propext','Classical.choice','Quot.sound'}
 roots=read('NGX_audit/batch0/proof0.json');fixtures=read('NGX_audit/fixtures/fixtures.json')
 assert roots['exit_status']==0 and {r['root'] for r in roots['results']}==set(read('NGX_AUDIT_ROOTS.json')['groups'][0])
 assert all(r['equal'] and set(r['walked_axioms'])<=standard for r in roots['results'])
 assert fixtures['exit_status']==0 and len(fixtures['results'])==8
 assert all(r['equal'] and (bool(r['walked_axioms']) if i<4 else not r['walked_axioms']) for i,r in enumerate(fixtures['results']))
 scan_path=E/'NGX_LOADED_scan.jsonl';raw=scan_path.read_bytes() if scan_path.exists() else lzma.decompress((E/'NGX_LOADED_scan.jsonl.xz').read_bytes())
 scan=[json.loads(l) for l in raw.splitlines()]
 assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
 assert read('NGX_L012/receipt.json')['exit_status']==0
 walker=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 assert sha(walker)==read('NGX_AUDIT_DRIVER_PINS.json')['walker_sha256']=='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
 assert sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for n,rc in [(5,0),(6,1)]:
  a=f'NGX_K{n:03}';r=read(a+'/receipt.json');ad=read(a+'-admission.json');log=(E/a/'stdout.log').read_text()
  assert r['exit_status']==rc and ad['exit']==0 and ad['reservation']['allowed'] is True
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  g=read(a+'-graph-check.json');l=read(a+'-lock-check.json');assert g['graph_matches_frozen'] and l['unchanged'] and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert set(next(p['features'] for p in g['selected_closure'] if p['name']=='aspis-r1-cost-probe'))=={'default','private-leaf-salts','optimized-terminal','program-build'}
  assert not read(a+'-source-check.json')['errors']
  assert ('VERIFICATION:- FAILED' if rc else 'VERIFICATION:- SUCCESSFUL') in log and 'timed out' not in log.lower()
  if rc:assert re.search(r'\*\* 1 of \d+ failed',log) and 'cfg!(NGX_invert)' in log
  for p,h in r['source_hashes'].items():assert sha((E/a/'sources'/p).read_bytes())==h
  source=(E/a/'sources/NGX_src/crates/aspis-r1-cost-probe/src/NGX_wire.rs').read_text();assert 'static mut' not in source and 'static ' not in source
 for a,n in [('NGX_L002','NGX_State'),('NGX_L004','NGX_StateImpl'),('NGX_L005','NGX_COMBINED_IMPORT')]:
  r=read(a+'/receipt.json');assert r['exit_status']==0 and sha((E/(n+'.lean')).read_bytes())==r['source_hashes']['NGX_generated/'+n+'.lean']
 baseline=json.loads(lzma.decompress((R/'evidence/ledger8-20261105/NGJ_LEDGER.json.xz').read_bytes()));closed=read('NGX_CLOSED.json');new=copy.deepcopy(baseline)
 assert len(closed['functions'])==1 and closed['functions'][0]['rows']==['TX1:146']
 for r in new['rows']:
  if r['row']=='TX1:146':
   assert r['composed_status']=='OPEN' and r['function']==closed['functions'][0]['function'];r['composed_status']='CLOSED';r['NGX_certificate']=closed['functions'][0]
 assert all(old==r for old,r in zip(baseline['rows'],new['rows']) if old['row']!='TX1:146')
 counts={k:sum(r['kind']==k for r in map(json.loads,(E/'NGX_ATTEMPTS.jsonl').read_text().splitlines())) for k in ['kani','extract']}
 attempts=list(map(json.loads,(E/'NGX_ATTEMPTS.jsonl').read_text().splitlines()));counts['lean_support']=sum(r['kind'] not in ['kani','extract'] for r in attempts)
 assert counts['kani']<=100 and counts['lean_support']<=70 and counts['extract']<=2
 return dict(status='PASS',new_rows=['TX1:146'],inherited_rows_preserved=len(baseline['rows'])-1,scan_modules=len(scan),raw_roots=len(roots['results']),fixtures=8,budget_used=counts,security_target_established=False)
if __name__=='__main__':
 result=validate();(E/'NGX_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1));print(json.dumps(result))
