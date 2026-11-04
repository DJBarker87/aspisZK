"""Validate persistence evidence without running a compiler or prover."""
from pathlib import Path
import hashlib,json,lzma,re,sys
E=Path(__file__).resolve().parent
ALLOW={'propext','Classical.choice','Quot.sound'}
def read(p):
 return json.loads((E/p).read_text())
def require(test,message):
 if not test:raise AssertionError(message)
rows=[json.loads(x) for x in (E/'NGR_ATTEMPTS.jsonl').read_text().splitlines()]
require(0<len(rows)<=50,'Lean/support budget')
require(len(set(r['attempt'] for r in rows))==len(rows),'duplicate attempt')
for r in rows:
 a=r['attempt'];c=read(a+'.json');ad=read(a+'-admission.json');receipt=read(a+'/receipt.json')
 require(ad['exit']==0 and ad['reservation']['allowed'] is True,'admission '+a)
 require(receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'caps '+a)
 require(receipt['exit_status']==r['exit_status'],'outcome '+a)
 require(receipt['swaps']=='0','swap '+a)
 require(c['timeout']==180,'timeout '+a)
 require(c['deps_fingerprint']['selected_objects'],'object pins '+a)
 require(any('/Aeneas/' in x for x in c['deps_fingerprint']['selected_objects']),'Aeneas pins '+a)
 for n,sha in receipt['source_hashes'].items():
  p=E/a/'sources'/n
  require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha,'snapshot '+a+' '+n)
 if c['kind']=='lean':
  require('-M7000' in c['command'],'Lean heap '+a)
  if not r['exit_status']:
   for line in receipt['print_axioms']:
    require('sorryAx' not in line,'recovery axiom '+a)
proof=read('NGR_audit/batch0/proof0.json');fixtures=read('NGR_audit/fixtures/fixtures.json')
roots=read('NGR_AUDIT_ROOTS.json')['groups'][0]
require(proof['exit_status']==0 and [r['root'] for r in proof['results']]==roots,'raw roots')
for r in proof['results']:
 require(r['equal'] and set(r['walked_axioms'])<=ALLOW,'axioms '+r['root'])
require(fixtures['exit_status']==0 and len(fixtures['results'])==8,'fixtures')
for i,r in enumerate(fixtures['results']):
 require(r['equal'] and bool(r['walked_axioms'])==(i<4),'fixture '+r['root'])
fixture_pin=read('NGR_L017/NGR_ProofDriver_BINARY_PIN.json')
for a in ['NGR_L018','NGR_L019']:
 require(read(a+'/NGR_ProofDriver_BINARY_PIN.json')==fixture_pin,'same binary '+a)
scan=[json.loads(l) for l in (E/'NGR_LOADED_scan.jsonl').read_text().splitlines()]
def coherent(rs):
 return all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rs)
require(coherent(scan),'coherent closure')
mutations=[]
for field,value in [('dangling',[{'missing':'NGR_Missing'}]),('duplicate_owners',[{'name':'NGR_WrongOwner'}]),('imports_match',False)]:
 bad=dict(scan[0]);bad[field]=value
 require(not coherent([bad]),'mutation denial '+field);mutations.append(field)
require(read('NGR_PIN_SHAPES.json')['status']=='PASS','object declaration shapes')
for row in read('NGR_PIN_SHAPES.json')['results']:
 require(not row['semantic_or_type_differences'] and row['proof_changes']==0,'object variation '+row['module'])
closure=lzma.decompress((E/'NGR_CLOSURE_PINS.json.xz').read_bytes())
require(hashlib.sha256(closure).hexdigest()==(E/'NGR_CLOSURE_PINS.json.sha256').read_text().strip(),'closure SHA')
require(not json.loads(closure)['comparisons']['NGP']['mismatches'],'NGP dependency identity')
for name in ['NGR_Data','NGR_WriterOutput','NGR_NativeCopy','NGR_HistoryPersist','NGR_COMBINED_IMPORT']:
 source=(E/(name+'.lean')).read_bytes()
 expected=['Init']+re.findall(r'^import ([\w.]+)',source.decode(),re.M)
 got=next(r['imports'] for r in scan if r['module']==name)
 require(got==expected,'source import baseline '+name)
 for r in reversed(rows):
  p=E/r['attempt']/'sources/NGR_generated'/(name+'.lean')
  if not r['exit_status'] and p.is_file():
   require(p.read_bytes()==source,'compiled final source '+name);break
 else:raise AssertionError('uncompiled '+name)
 require(not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',source.decode(),re.M),'source discipline '+name)
# Source-based import identity must reject removal of the implicit Init import.
r=next(r for r in scan if r['module']=='NGR_HistoryPersist')
expected=['Init']+re.findall(r'^import ([\w.]+)',(E/'NGR_HistoryPersist.lean').read_text(),re.M)
require(r['imports'][1:]!=expected,'missing Init denial');mutations.append('missing implicit Init')
bad=dict(proof['results'][0]);bad['walked_axioms']=['sorryAx']
require(not set(bad['walked_axioms'])<=ALLOW,'axiom mutation denial');mutations.append('nonstandard axiom')
for p in E.rglob('*'):
 if p.is_file():require(p.stat().st_size<=20_000_000,'oversize '+str(p))
 require(p.name!='__pycache__','bytecode '+str(p))
result=dict(status='PASS',attempts=len(rows),successes=sum(r['exit_status']==0 for r in rows),excluded=[r['attempt'] for r in rows if r['exit_status']],roots=len(roots),fixtures=8,modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),compatible_cached_replicas=sum(len(r['cached_replicas']) for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,denied_evidence_mutations=mutations)
print(json.dumps(result,indent=1))
