"""Validate this job's receipts and explicit non-promotion claims."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NIA_L[0-9][0-9][0-9]/receipt.json'))]
assert receipts and len(receipts)<=80
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits,(r['attempt'],r['limits'])
 assert int(r['swaps'])==0,r['attempt']
 a=json.loads((E/(r['attempt']+'-admission.json')).read_text())
 assert a['exit']==0 and a['reservation']['allowed'] is True,r['attempt']
 for source,h in r['source_hashes'].items():
  p=E/r['attempt']/'sources'/source
  assert p.is_file() and sha(p)==h,(r['attempt'],source)
 assert r['source_revision'] and r['deps_fingerprint'],r['attempt']
for p in E.glob('NIA_*.lean'):
 if p.stem in ['NIA_Driver','NIA_ProofDriver']:continue
 raw=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',raw),p
 candidates=[r for r in receipts if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0]
 assert candidates,p
 latest=candidates[-1]
 assert latest['source_hashes'].get('NIA_generated/'+p.name)==sha(p),p
 for line in latest['print_axioms']:
  if 'depends on axioms:' in line:
   names=set(line.split('depends on axioms: [')[1].rstrip(']').replace(' ','').split(','))
   assert names<={'propext','Classical.choice','Quot.sound'},(p,line)
proof=json.loads((E/'NIA_audit/batch0/proof0.json').read_text())
assert proof['exit_status']==0
expected=json.loads((E/'NIA_AUDIT_ROOTS.json').read_text())['groups'][0]
assert [r['root'] for r in proof['results']]==expected
for r in proof['results']:
 assert r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},r
fixtures=json.loads((E/'NIA_audit/fixtures/fixtures.json').read_text())
assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for i,r in enumerate(fixtures['results']):
 assert r['equal'] and r['walked_axioms']==r['collect_axioms'],r
 assert bool(r['walked_axioms'])==(i<4),r
scan=[json.loads(s) for s in (E/'NIA_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
assert json.loads((E/'NIA_audit/scan/scan.json').read_text())['exit_status']==0
assert json.loads((E/'NIA_LEDGER_DELTA.json').read_text())['row_promotions']==[]
assert not list(E.rglob('__pycache__'))
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
print(json.dumps({'status':'PASS','scopes':len(receipts),'roots':len(expected),'fixtures':8,'scan_modules':len(scan),'row_promotions':0}))
