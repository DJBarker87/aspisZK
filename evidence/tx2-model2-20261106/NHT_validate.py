"""Strict compile-free validation of conditional model evidence, never native credit."""
from pathlib import Path
import json,hashlib,re,lzma,subprocess,copy
E=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def admission(x):
 assert x['exit']==0 and x['reservation']['allowed'] is True

def main():
 audit=json.loads((E/'NHT_AUDIT.json').read_text())
 records=[json.loads(l) for l in (E/'NHT_ATTEMPTS.jsonl').read_text().splitlines()]
 assert len(records)==len({x['attempt'] for x in records})<=80
 for row in records:
  a=row['attempt'];rc=json.loads((E/a/'receipt.json').read_text())
  assert rc['exit_status']==row['exit_status']
  admission(json.loads((E/(a+'-admission.json')).read_text()))
  assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert int(rc['swaps'])==0
  if rc['kind']=='lean':assert '-M7000' in rc['command']
  for rel,h in rc['source_hashes'].items():
   p=E/a/'sources'/rel
   if p.exists():assert sha(p)==h,(a,rel)
   else:
    ref=json.loads((E/'NHT_PACK.json').read_text())[str(p.relative_to(E))]
    q=E/ref['canonical'];assert sha(q)==h==ref['sha256']
 for name,a in audit['selected'].items():
  row=json.loads((E/a/'receipt.json').read_text());assert row['exit_status']==0
  assert row['source_hashes']['NHT_generated/'+name+'.lean']==sha(E/(name+'.lean'))
  assert 'sorryAx' not in (E/a/'stdout.log').read_text()
  for line in row['print_axioms']:
   if 'depends on axioms:' in line:
    assert set(re.findall(r'\[([^]]*)\]',line)[0].split(', '))<=ALLOWED
 roots=[r for g in json.loads((E/'NHT_AUDIT_ROOTS.json').read_text())['groups'] for r in g]
 observed=[]
 binary=json.loads((E/'NHT_L056/NHT_ProofDriver_BINARY_PIN.json').read_text())
 for i in range(7):
  a=f'NHT_L{57+i:03d}';rc=json.loads((E/a/'receipt.json').read_text());assert rc['exit_status']==0
  assert json.loads((E/a/'NHT_ProofDriver_BINARY_PIN.json').read_text())==binary
  x=json.loads((E/f'NHT_audit/batch{i}/proof{i}.json').read_text());assert x['exit_status']==0
  for row in x['results']:
   assert row['equal'] is True and set(row['walked_axioms'])<=ALLOWED
   observed.append(row['root'])
 assert observed==roots
 f=json.loads((E/'NHT_audit/fixtures/fixtures.json').read_text());assert f['exit_status']==0 and len(f['results'])==8
 expected=['NEP_Planted.matchAx','NEP_Planted.privateAx','NEP_Planted.proofAx','NEP_Planted.auxAx']
 for i,row in enumerate(f['results']):
  assert row['equal'] is True and row['walked_axioms']==([expected[i]] if i<4 else [])
 scan=[json.loads(l) for l in (E/'NHT_LOADED_scan.jsonl').read_text().splitlines()]
 assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
 assert audit['scan_exit']==0 and audit['promotions']==0
 assert json.loads((E/'NHT_LEDGER_DELTA.json').read_text())['promotions']==[]
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
 assert not list(E.rglob('__pycache__'))
 for p in E.glob('NHT_*.lean'):
  if p.stem.endswith('Driver'):continue
  assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',p.read_text()),p
  assert 'maxHeartbeats' not in p.read_text() and 'maxRecDepth' not in p.read_text()
 for p,record in json.loads((E/'NHT_INPUTS.json').read_text())['files'].items():assert sha(Path(p))==record['sha256']
 assert json.loads((E/'NHT_AUDIT_PROVENANCE.json').read_text())['byte_identical'] is True
 closure=lzma.decompress((E/'NHT_CLOSURE_PINS.json.xz').read_bytes())
 assert hashlib.sha256(closure).hexdigest()==(E/'NHT_CLOSURE_PINS.json.sha256').read_text().strip()
 closure=json.loads(closure)
 assert closure['modules']==len(scan) and len(closure['files'])>=len(scan)
 exports=json.loads((E/'NHT_EXPORT.json').read_text())
 assert exports['closure_files']==len(closure['files']) and exports['own_exports']
 shipped=json.loads((E/'NHT_SHIPPED_IDENTITY.json').read_text());assert all(x['equal'] for x in shipped.values())
 mutations=0
 good={'exit':0,'reservation':{'allowed':True}}
 for key,value in [('exit',78),('exit',1),('allowed',False),('allowed',None),('allowed',1)]:
  bad=copy.deepcopy(good)
  if key=='exit':bad['exit']=value
  else:bad['reservation']['allowed']=value
  try:admission(bad)
  except (AssertionError,KeyError):mutations+=1
  else:raise AssertionError('accepted admission mutation')
 result={'status':'PASS conditional model evidence; no native promotions','scopes':len(records),'raw_roots':len(roots),'fixtures':8,'scan_modules':len(scan),'admission_mutations_rejected':mutations}
 (E/'NHT_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
