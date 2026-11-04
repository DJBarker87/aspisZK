"""Validate committed receipts, source snapshots, raw audit and coherent imports."""
from pathlib import Path
import hashlib,json,lzma,re
E=Path(__file__).resolve().parent
ALLOW={'propext','Classical.choice','Quot.sound'}
def read(p):return json.loads((E/p).read_text())
def require(test,message):
 if not test:raise AssertionError(message)
rows=[json.loads(l) for l in (E/'NGS_ATTEMPTS.jsonl').read_text().splitlines()]
require(0<len(rows)<=50,'scope budget')
require(len({r['attempt'] for r in rows})==len(rows),'duplicate attempt')
for r in rows:
 a=r['attempt'];cfg=read(a+'.json');ad=read(a+'-admission.json');rc=read(a+'/receipt.json')
 require(ad['exit']==0 and ad['reservation']['allowed'] is True,'admission '+a)
 require(rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'caps '+a)
 require(rc['exit_status']==r['exit_status'] and rc['swaps']=='0','result/swap '+a)
 require(cfg['timeout']==180,'timeout '+a)
 require(cfg['deps_fingerprint']['selected_objects'],'object pins '+a)
 require(any('/Aeneas/' in p for p in cfg['deps_fingerprint']['selected_objects']),'Aeneas pin '+a)
 for n,sha in rc['source_hashes'].items():
  p=E/a/'sources'/n;require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha,'snapshot '+a+' '+n)
 if cfg['kind']=='lean':
  require('-M7000' in cfg['command'],'heap '+a)
  if rc['exit_status']==0:
   for line in rc['print_axioms']:require('sorryAx' not in line,'recovery axiom '+a)
roots=read('NGS_AUDIT_ROOTS.json')['groups'];total=0
for i in range(len(roots)):
 v=read(f'NGS_audit/batch{i}/proof{i}.json')
 require(v['exit_status']==0 and [r['root'] for r in v['results']]==roots[i],'raw roots')
 for r in v['results']:require(r['equal'] and set(r['walked_axioms'])<=ALLOW,'raw axioms '+r['root'])
 total+=len(v['results'])
v=read('NGS_audit/fixtures/fixtures.json');require(v['exit_status']==0 and len(v['results'])==8,'fixtures')
for i,r in enumerate(v['results']):require(r['equal'] and bool(r['walked_axioms'])==(i<4),'fixture '+r['root'])
for a in ['NGS_L012','NGS_L015','NGS_L016']:
 require(read(a+'/NGS_ProofDriver_BINARY_PIN.json')==read('NGS_L011/NGS_ProofDriver_BINARY_PIN.json'),'same binary '+a)
scan=[json.loads(l) for l in (E/'NGS_LOADED_scan.jsonl').read_text().splitlines()]
def coherent(rs):return all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rs)
require(coherent(scan),'coherent closure')
mutations=[]
for field,value in [('dangling',[{'missing':'NGS_Missing'}]),('duplicate_owners',[{'name':'NGS_WrongOwner'}]),('imports_match',False)]:
 bad=dict(scan[0]);bad[field]=value;require(not coherent([bad]),'mutation '+field);mutations.append(field)
closure=lzma.decompress((E/'NGS_CLOSURE_PINS.json.xz').read_bytes())
require(hashlib.sha256(closure).hexdigest()==(E/'NGS_CLOSURE_PINS.json.sha256').read_text().strip(),'closure SHA')
comparison=json.loads(closure)['NGR_comparison'];require(not comparison['missing'] and not comparison['mismatches'],'NGR identity')
modules=['NGS_Selection','NGS_CheckpointRead','NGS_Carriers','NGS_IssuedCarriers','NGS_PersistedCarriers','NGS_COMBINED_IMPORT']
for name in modules:
 source=(E/(name+'.lean')).read_bytes();expected=['Init']+re.findall(r'^import ([\w.]+)',source.decode(),re.M)
 got=next(r['imports'] for r in scan if r['module']==name);require(got==expected,'source baseline '+name)
 for r in reversed(rows):
  p=E/r['attempt']/'sources/NGS_generated'/(name+'.lean')
  if r['exit_status']==0 and p.is_file():require(p.read_bytes()==source,'final compiled '+name);break
 else:raise AssertionError('uncompiled '+name)
 require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',source.decode(),re.M),'source discipline '+name)
 expected_sha=hashlib.sha256(source).hexdigest()
 require(any(r['module']==name and r['source_sha256']==expected_sha for r in read('NGS_EXPORT.json')),'export source '+name)
r=next(r for r in scan if r['module']=='NGS_Carriers')
require(r['imports'][1:]!=['Init']+re.findall(r'^import ([\w.]+)',(E/'NGS_Carriers.lean').read_text(),re.M),'Init mutation');mutations.append('missing implicit Init')
require(not {'sorryAx'}<=ALLOW,'axiom mutation');mutations.append('nonstandard axiom')
for p in E.rglob('*'):
 if p.is_file():require(p.stat().st_size<=20_000_000,'oversize '+str(p))
 require(p.name!='__pycache__','bytecode '+str(p))
require(not read('NGS_SOURCE_FREEZE.json')['differences'],'frozen source')
print(json.dumps(dict(status='PASS',attempts=len(rows),successes=sum(r['exit_status']==0 for r in rows),excluded=[r['attempt'] for r in rows if r['exit_status']],roots=total,fixtures=8,modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,NGR_shared_objects=comparison['shared_NGR_objects'],denied_evidence_mutations=mutations),indent=1))
