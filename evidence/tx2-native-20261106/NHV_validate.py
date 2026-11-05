"""Additive NHV evidence checks; no baseline admission predicate is relaxed."""
from pathlib import Path
import json,hashlib,lzma,re,sys,copy
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(ad,rc,graph,lock):
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,'admission'
 assert graph['graph_matches_frozen'] is True,'graph'
 assert graph['lock_sha256']==lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef' and lock['unchanged'] is True,'lock'
 argv=rc['command'];assert argv==['python3','NHV_gate.py',rc['attempt']+'.json']
 x=json.loads((E/(rc['attempt']+'.json')).read_text())
 assert x['env']['CARGO_NET_OFFLINE']=='true'
 assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert x['native_command'][x['native_command'].index('--harness-timeout')+1]=='90s'
 assert '--locked' not in x['native_command']
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'limits'
 assert graph.get('all_crate_features'),'complete feature graph'
 f={r['name']:set(r['features']) for r in graph['all_crate_features']}
 assert f['aspis-r1-cost-probe']=={'default','private-leaf-salts','optimized-terminal','program-build'},'deployed library features'
 assert f['aspis-core']=={'r0'},'deployed core features'
 statement={'pool-v1-kernel','r0','spend-dynamic-rate512','pool-v1-pair-forest-active-mask-basis-audit','pool-v1-pair-forest-binary-copy-weights-audit','pool-v1-pair-forest-copy-finish-dot-basis-audit','pool-v1-pair-forest-copy-pattern-basis-audit','pool-v1-pair-forest-copy-selector-tensor-basis-audit','pool-v1-pair-forest-copy-tag-dot-basis-audit','pool-v1-pair-forest-endpoint-selector-cache-audit','pool-v1-pair-forest-packed-digest-audit','pool-v1-pair-forest-packed-digest-selector-tensor-audit','pool-v1-pair-forest-packed-range-audit','pool-v1-pair-forest-pattern-window-audit','pool-v1-pair-forest-semantic-factor-audit'}
 assert f['aspis-statement']==statement,'deployed statement features'
 assert '--features' in x['native_command'] and x['native_command'][x['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
 for n,pin in json.loads((E/rc['attempt']/'sources/NHV_SOURCE_PINS.json').read_text()).items():
  assert sha(E/rc['attempt']/'sources/NHV_src'/n)==pin,('source',n)
 return True

def main():
 receipts=[]
 for p in sorted(E.glob('NHV_[KLE][0-9][0-9][0-9]/receipt.json')):
  r=json.loads(p.read_text());a=r['attempt'];receipts.append(r)
  ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert r['source_revision'] and r.get('wall_seconds') is not None and r.get('peak_rss_kib') is not None and str(r.get('swaps'))=='0'
  if r['kind']=='kani':check(ad,r,json.loads((E/(a+'-graph-check.json')).read_text()),json.loads((E/(a+'-lock-check.json')).read_text()))
 counts={k:sum(r['kind']==k for r in receipts) for k in ['kani','extract']};counts['lean_support']=len(receipts)-counts['kani']-counts['extract'];assert counts['kani']<=120 and counts['extract']<=1 and counts['lean_support']<=80
 baseline=json.loads((E/'NHV_BASELINE_BOUNDARIES.json').read_text());assert sha(ROOT/'evidence/ledger10-20261106/NHO_LEDGER.json.xz')==baseline['baseline_sha256']
 ledger=json.loads(lzma.decompress((ROOT/'evidence/ledger10-20261106/NHO_LEDGER.json.xz').read_bytes()));assert next(r for r in ledger['rows'] if r['row']=='TX2:065')['composed_status']=='OPEN'
 assert json.loads((E/'NHV_SHIPPED_IDENTITY.json').read_text())['unchanged'] is True
 assert json.loads((E/'NHV_CLOSED.json').read_text())['new_composed_rows']==0
 delta=json.loads((E/'NHV_LEDGER_DELTA.json').read_text());assert delta['row']=='TX2:065' and delta['after']=='OPEN' and delta['promotions']==[]
 assert sha(ROOT/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for rel,pin in json.loads((E/'NHV_INPUT_PINS.json').read_text()).items():assert sha(ROOT/rel)==pin['sha256']
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=20*1024**2,('oversize',str(p))
 audit=json.loads((E/'NHV_AUDIT.json').read_text())
 if audit.get('status','').startswith('PASS'):
  expected={n for g in json.loads((E/'NHV_AUDIT_ROOTS.json').read_text())['groups'] for n in g}
  assert {r['root'] for r in audit['roots']}==expected and len(audit['roots'])==127
  for row in audit['roots']:assert row['equal'] is True and set(row['walked_axioms'])==set(row['collect_axioms']) and set(row['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  scan=[json.loads(l) for l in (E/'NHV_LOADED_scan.jsonl').read_text().splitlines()]
  assert len(scan)==audit['scanner']['modules'] and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
  fixture=json.loads((E/'NHV_audit/fixtures/fixtures.json').read_text());assert fixture['exit_status']==0 and len(fixture['results'])==8
  pin=json.loads((E/'NHV_L068/NHV_ProofDriver_BINARY_PIN.json').read_text())
  for n in range(69,76):assert json.loads((E/f'NHV_L{n:03}/NHV_ProofDriver_BINARY_PIN.json').read_text())==pin
  for n in ['NHV_CACHE_VERIFICATION.json','NHV_SOURCE_VERIFICATION.json']:assert json.loads((E/n).read_text())['status']=='PASS'
  assert 'CBMC timed out' in (E/'NHV_K118/stdout.log').read_text()
  assert json.loads((E/'NHV_PACKET_STATUS.json').read_text())['query']['raw']['credit'] is False
 for rc in receipts:
  for n,h in rc['source_hashes'].items():assert sha(E/rc['attempt']/'sources'/n)==h,(rc['attempt'],n)
 report=dict(status='PASS',counts=counts,receipts=len(receipts),promotions=0,baseline_checks='unchanged NHO/NDT inherited; NHV adds provenance/resource/lock/zero-promotion checks only')
 (E/'NHV_VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
