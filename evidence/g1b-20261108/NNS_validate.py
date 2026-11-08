"""Validate committed proof inputs against successful receipts; metadata only."""
from pathlib import Path
import json,hashlib,re,csv
E=Path(__file__).resolve().parent
accepted={};failures=[];receipts=[]
for p in sorted(E.glob('NNS_L*/receipt.json')):
 r=json.loads(p.read_text());receipts.append(r)
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text())
 assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 disk=json.loads((E/(r['attempt']+'-disk-0.json')).read_text());assert disk['free']>=40_000_000_000
 if r['kind']=='lean':assert all(x in r['command'] for x in ['-j1','-M7000','-DElab.async=false'])
 if r['exit_status']!=0:failures.append(r['attempt']);continue
 if r['kind']=='lean':
  p0=E/(r['module']+'.lean')
  if p0.exists() and hashlib.sha256(p0.read_bytes()).hexdigest() in r['source_hashes'].values():accepted[r['module']]=r
modules=[p for p in E.glob('NNS_*.lean')]
assert {p.stem for p in modules}==set(accepted),({p.stem for p in modules}-set(accepted))
roots=[]
for p in modules:
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s),p
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s)
 ns=re.search(r'^namespace (\S+)',s,re.M)
 if not ns:continue
 for t in re.findall(r'^theorem (\w+)',s,re.M):
  name=ns[1]+'.'+t;roots.append(name)
  assert '#print axioms '+t in s,(p,t)
  assert any("'"+name+"'" in l for l in accepted[p.stem]['print_axioms']),name
events=[json.loads(l) for l in (E/'NNS_ATTEMPTS.jsonl').read_text().splitlines()]
for r in receipts:
 checks=[x for x in events if x.get('attempt')==r['attempt'] and x.get('event')=='share_check']
 assert checks and checks[-1]['host']['count']<6
assert len(receipts)<=30
out=dict(status='PASS',accepted_modules=len(modules),roots=sorted(roots),scope_receipts=len(receipts),failed_scopes=failures,requested_main_roots_delivered=False,shipped_files_changed=False)
(E/'NNS_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
with(E/'NNS_COMPILE.tsv').open('w')as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['attempt','target','exit','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','deps_fingerprint','print_axioms','receipt'])
 for r in receipts:
  path=r['attempt']+'/receipt.json';w.writerow([r['attempt'],r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r['source_hashes']),path,json.dumps(r['print_axioms']),path])
print(json.dumps({k:v for k,v in out.items()if k!='roots'}))
