"""Audit budget/source/receipt integrity; this does not rerun a proof or release gate."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027';t=json.loads((out/'TALLY.json').read_text())
assert len(t['used_ids'])==len(set(t['used_ids'])) and all(39600<=i<=39899 for i in t['used_ids'])
assert t['next_id']==max(t['used_ids'],default=39599)+1
assert len(t['lean_charged'])<=100 and len(t['kani_charged'])<=10
rows=[]
for a in t['lean_charged']:
 p=out/f'{a}.json';r=json.loads(p.read_text());s=(out/r['source_snapshot']).read_bytes()
 assert hashlib.sha256(s).hexdigest()==r['source_sha256'],a
 assert r['limits']['lean_M']==7000 and r['limits']['MemoryMax']=='8G' and r['limits']['MemorySwapMax']==0
 if r['exit']==0:
  for line in r.get('axioms',[]):
   if 'depends on axioms:' in line:
    words=set(re.findall(r'(?:propext|Classical\.choice|Quot\.sound|sorryAx|[A-Za-z_]+Ax)',line))
    assert words<={'propext','Classical.choice','Quot.sound'},(a,line)
 rows.append({'attempt':a,'module':r['module'],'exit':r['exit'],'wall':r['wall'],'peak_rss_kib':r['peak_rss_kib'],'swap':r['swap'],'revision':r['source_revision'],'axioms':r['axioms']})
for p in (root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_CBL_*.lean'):
 s=p.read_text()
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b',s,re.M),p
 assert not re.search(r'\b(?:native_decide|implemented_by)\b',s),p
 for name in re.findall(r'^theorem\s+(\w+)',s,re.M):assert '#print axioms '+name in s,(p,name)
f='crates/aspis-r1-cost-probe/src/host_commitment.rs';base=subprocess.check_output(['git','show','bd47052f039ae2d96060acb5607fe652ebe193d4:'+f],cwd=root);now=(root/f).read_bytes()
assert now.startswith(base) and now[len(base):].lstrip().startswith(b'#[cfg(kani)]\nmod pv_cblib_library_checks')
for key,r in json.loads((out/'source-provenance.json').read_text())['libraries'].items():
 assert hashlib.sha256((out/'source'/key.replace('/','__')).read_bytes()).hexdigest()==r['sha256']
result={'status':'pass','scope':'receipt/source/budget integrity only; not native equivalence, kernel replay or deployed privacy','lean_charged':len(t['lean_charged']),'kani_charged':len(t['kani_charged']),'next_id':t['next_id'],'lean_receipts':rows}
if '--check' not in sys.argv:(out/'receipt-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='lean_receipts'}))
