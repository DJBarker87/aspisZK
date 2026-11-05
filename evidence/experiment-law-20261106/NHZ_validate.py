"""Validate committed receipt coherence; mutations test rejection gates."""
from pathlib import Path
import json,hashlib,lzma,re,copy
E=Path(__file__).resolve().parent
STANDARD={'propext','Classical.choice','Quot.sound'}
def require(ok,msg):
 if not ok:raise AssertionError(msg)
def receipt(r,ad):
 require(ad['exit']==0 and ad['reservation'].get('allowed') is True,'admission')
 require(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'caps')
 require(str(r['swaps'])=='0','swap')
 require(r['source_revision'] and r['source_hashes'] and r['deps_fingerprint']['selected_objects'],'pins')
 if r['kind']=='lean':require('-M7000' in r['command'] and r['command'][1:3]==['env','lean'],'lean command')
def scan_good(rows):require(all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows),'scan')
def audit_good(x):
 require(x['exit_status']==0 and x['results'],'audit result')
 for r in x['results']:require(r['equal'] and set(r['walked_axioms'])<=STANDARD,'axioms')
entries=[json.loads(l) for l in (E/'NHZ_ATTEMPTS.jsonl').read_text().splitlines()]
require(len(entries)<=70 and len({r['attempt'] for r in entries})==len(entries),'budget/attempt uniqueness')
for row in entries:
 a=row['attempt'];r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-admission.json')).read_text());receipt(r,ad)
 for source,expected in r['source_hashes'].items():
  p=E/a/'sources'/source;require(hashlib.sha256(p.read_bytes()).hexdigest()==expected,'snapshot '+source)
# Final proof/source identity: only successful final sources are credited.
final={'NHZ_NativeAssociation':'NHZ_L001','NHZ_SameLaw':'NHZ_L006','NHZ_ScalarEvents':'NHZ_L008','NHZ_Realization':'NHZ_L009','NHZ_CheckpointEvents':'NHZ_L011','NHZ_Obstruction':'NHZ_L016','NHZ_COMBINED_IMPORT':'NHZ_L017'}
for module,a in final.items():
 r=json.loads((E/a/'receipt.json').read_text());require(r['exit_status']==0,'final exit')
 require((E/(module+'.lean')).read_bytes()==(E/a/'sources/NHZ_generated'/(module+'.lean')).read_bytes(),'final source '+module)
 log=(E/a/'stdout.log').read_text();require('sorryAx' not in log and 'error:' not in log,'final log')
 source=(E/(module+'.lean')).read_text();require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source),'source admission')
 for name in re.findall(r'^theorem (\w+)',source,re.M):require('#print axioms '+name in source,'print '+name)
fixtures=json.loads((E/'NHZ_audit/fixtures/fixtures.json').read_text());require(fixtures['exit_status']==0 and len(fixtures['results'])==8,'fixtures')
for i,row in enumerate(fixtures['results']):
 require(row['equal'] and row['walked_axioms']==row['collect_axioms'],'fixture compare')
 require((len(row['walked_axioms'])==1 and row['walked_axioms'][0].startswith('NEP_Planted.')) if i<4 else row['walked_axioms']==[],'fixture expected')
roots=json.loads((E/'NHZ_audit/batch0/proof0.json').read_text());audit_good(roots)
expected=json.loads((E/'NHZ_AUDIT_ROOTS.json').read_text())['groups'][0];require([r['root'] for r in roots['results']]==expected,'root list')
for a in ['NHZ_L019','NHZ_L020','NHZ_L021','NHZ_L022']:
 p=json.loads((E/a/'NHZ_ProofDriver_BINARY_PIN.json').read_text());require(p==json.loads((E/'NHZ_L019/NHZ_ProofDriver_BINARY_PIN.json').read_text()),'same binary')
scan=[json.loads(l) for l in (E/'NHZ_LOADED_scan.jsonl').read_text().splitlines()];scan_good(scan)
require(json.loads((E/'NHZ_audit/scan/scan.json').read_text())['exit_status']==0,'scan exit')
raw=lzma.decompress((E/'NHZ_CLOSURE_PINS.json.xz').read_bytes());require(hashlib.sha256(raw).hexdigest()==(E/'NHZ_CLOSURE_PINS.json.sha256').read_text().strip(),'closure hash')
closure=json.loads(raw);require(any(r['module'].startswith('Aeneas') for r in closure['selected_objects']),'Aeneas closure')
require(json.loads((E/'NHZ_LEDGER_DELTA.json').read_text())['row_promotions']==[],'no promotions')
require(not list(E.rglob('__pycache__')),'pycache');require(not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024],'size')
mutations=[]
def rejects(name,f):
 try:f()
 except AssertionError:mutations.append(dict(name=name,rejected=True));return
 raise AssertionError('accepted mutation '+name)
r=json.loads((E/'NHZ_L017/receipt.json').read_text());ad=json.loads((E/'NHZ_L017-admission.json').read_text())
bad=copy.deepcopy(ad);bad['reservation']['allowed']=False;rejects('allowed_false',lambda:receipt(r,bad))
badR=copy.deepcopy(r);badR['limits']['memory.swap.max']='1';rejects('swap_cap',lambda:receipt(badR,ad))
badA=copy.deepcopy(roots);badA['results'][0]['walked_axioms'].append('Injected.axiom');rejects('custom_axiom',lambda:audit_good(badA))
badS=copy.deepcopy(scan);badS[0]['dangling']=[{'missing':'Injected'}];rejects('dangling',lambda:scan_good(badS))
summary=dict(status='PASS',attempts=len(entries),Kani=0,extraction=0,final_sources=final,roots=len(expected),fixtures=8,scan_modules=len(scan),scan_declarations=sum(r['declarations'] for r in scan),scan_references=sum(r['edges'] for r in scan),cached_replicas=sum(len(r['cached_replicas']) for r in scan),defects=0,closure_files=len(closure['selected_objects']),mutations=mutations)
(E/'NHZ_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
