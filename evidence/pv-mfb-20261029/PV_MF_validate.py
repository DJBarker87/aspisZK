"""Integrity checks for D495; does not invoke Lean or any build."""
from pathlib import Path
import hashlib,json,lzma,subprocess,collections,importlib.util
D=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('c',str(D.parent/'pv-mf-20261029/PV_MF_check.py'));c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c)
def load(n):
 p=D/n
 return json.load(open(p)) if p.exists() else json.load(lzma.open(str(p)+'.xz'))
stale=c.load('STALE.json');r=load('classifications.json');summary=load('summary.json');assert len(r)==len(stale)==764
assert [x['input'] for x in r]==stale
assert [x['record'] for x in r]==list(range(1,765))
assert dict(collections.Counter(x['category'] for x in r))==summary['counts']
assert all(x['category'] in ['A','B','C'] and x['reason'] for x in r)
possible=load('candidate-traces.json');hit={h['record'] for row in possible for h in row['hits']}
for x in r:
 if x['category']=='B' and x['input']['path'].endswith('.lean'):assert x['record'] not in hit,x['record']
 assert x['current_blob']==subprocess.check_output(['git','rev-parse','HEAD:'+x['input']['path']],text=True).strip(),x['record']
for p in D.glob('*.json.sha256'):
 raw=lzma.open(str(p).removesuffix('.sha256')+'.xz').read();assert hashlib.sha256(raw).hexdigest()==p.read_text().split()[0],p
accepted=[]
for p in D.glob('lean-*/result.json'):
 z=json.load(open(p))
 if z.get('preflight_version')!='complete-h4':continue
 q=p.parent;receipt=json.load(open(q/'receipt/receipt.json'));pre=json.load(open(q/'preflight.json'))
 assert z['exit']==receipt['exit_status']==0
 assert pre['external_transitive_objects_checked']==5673
 assert len(z['axioms'])==1 and 'sorryAx' not in z['axioms'][0]
 for g in ['admission.json','barrier.json']:assert json.load(open(q/g))['allowed'] is True
 lim=receipt['limits'];assert lim['memory.swap.max']=='0' and lim['memory.max']=='8589934592'
 assert receipt['swaps']==0
 accepted.append(z['row'])
assert sorted(accepted)==summary['checked_closures'] and len(accepted)==4
assert summary['lean_invocations']==len(list(D.glob('lean-*/result.json')))==8
assert not summary['failing_closures']
changed=subprocess.check_output(['git','diff','--name-only','a8ecbe80fd8057a68519b93dae232cf950dc222a'],text=True).splitlines()
assert all(p.startswith('evidence/pv-mfb-20261029/') for p in changed),changed
assert not [p for p in D.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print(json.dumps(dict(integrity='PASS',records=764,categories=summary['counts'],accepted_checks=accepted,invocations=8,no_source_edits=True),indent=2))
