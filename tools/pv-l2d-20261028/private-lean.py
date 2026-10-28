"""Per-module private source submission through the unchanged shared run2.py.
SHA-frozen project dependencies are built here, never imported from CX caches.
"""
from pathlib import Path
import sys,json,subprocess,hashlib,shlex,re,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
H='/home/dombarker/project-offloads/codex-pv-l2d-20261028';P=H+'/embedding';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);m=sys.argv[2];assert 51500<=a<=51599
assert not (E/f'receipt-{a}.json').exists()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
resolution=json.loads((E/'embedding-resolution.json').read_text())
if (E/'sampler-resolution.json').exists():resolution['resolved'].update(json.loads((E/'sampler-resolution.json').read_text())['resolved'])
if m.startswith('PV_L2D_'):
 s=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');b=s.read_bytes();authority='own git-tracked new module'
 assert b==subprocess.check_output(['git','show',rev+':'+str(s.relative_to(R))])
else:
 v=resolution['resolved'][m];s=R/v['path'];b=s.read_bytes();authority=v['authority']
 assert hashlib.sha256(b).hexdigest()==v['sha256']
sha=hashlib.sha256(b).hexdigest()
def transport(args):
 for retry in range(11):
  q=subprocess.run(args,text=True,capture_output=True)
  if q.returncode!=255:return q
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,stderr=q.stderr))+'\n')
  if retry==10:raise RuntimeError('ten transient retries exhausted')
  time.sleep(60)
def ssh(c):return transport(['ssh',host,c])
code='''import pathlib,re,json
r=pathlib.Path('/home/dombarker/project-offloads');pat=re.compile(r'(^|[-_])ID([-_.]|$)');hits=[]
for d in r.glob('codex-pv-*'):
 if d.name=='codex-pv-l2d-20261028':continue
 for p in d.glob('**/*ID*'):
  if p.is_file() and pat.search(p.name):hits.append(str(p))
sent=r/'r1-privacy-build-integration-20261019/evidence/sent.txt'
print(json.dumps(dict(other_receipts=hits,sent_hits=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]=='ID'])))
'''.replace('ID',str(a))
q=ssh('python3 -c '+shlex.quote(code));assert q.returncode==0,q.stderr
v=json.loads(q.stdout);(E/f'id-audit-{a}.json').write_text(json.dumps(v,indent=2)+'\n');assert not v['other_receipts'] and not v['sent_hits'],v
q=ssh(f'mkdir -p {H}/evidence\npython3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/evidence/admission-{a}.json > {H}/evidence/admission-{a}.log 2>&1\npv_status=$?\ncat {H}/evidence/admission-{a}.log\nexit $pv_status')
(E/f'admission-{a}.log').write_text(q.stdout+q.stderr);ad=json.loads(q.stdout.strip().splitlines()[-1])
if q.returncode!=0 or not ad['allowed']:
 (E/f'refusal-{a}.json').write_text(json.dumps(dict(epoch=time.time(),**ad),indent=2)+'\n');print('REFUSED',ad);sys.exit(78)
rel=m.replace('.','/')
q=ssh(f'mkdir -p {P}/sources/'+str(Path(rel).parent)+f' {P}/objects/'+str(Path(rel).parent));assert q.returncode==0
q=transport(['scp','-q',str(s),f'{host}:{P}/sources/{rel}.lean']);assert q.returncode==0,q.stderr
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-l2d-private-'+str(a),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/evidence/time-{a}.log','timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',P+'/J.json',P+'/objects',P+'/sources',P+'/objects/'+rel+'.olean',P+'/sources/'+rel+'.lean','7000']
v=dict(attempt=a,target=m,source_revision=rev,source_path=str(s.relative_to(R)),source_git_blob=subprocess.check_output(['git','rev-parse',rev+':'+str(s.relative_to(R))],text=True).strip(),source_sha256=sha,source_authority=authority,command=cmd,admission=ad,external_preflight='embedding-external-check.json',foreign_project_objects_loaded=False)
(E/f'launch-{a}.json').write_text(json.dumps(v,indent=2)+'\n')
q=subprocess.run(['ssh',host,shlex.join(cmd)+f' > {H}/evidence/out-{a}.log 2>&1'],text=True,capture_output=True);v['scope_exit']=q.returncode
for kind in ['out','time']:
 r=ssh(f'cat {H}/evidence/{kind}-{a}.log');assert r.returncode==0,r.stderr;(E/f'{kind}-{a}.log').write_text(r.stdout)
t=(E/f'time-{a}.log').read_text();out=(E/f'out-{a}.log').read_text();print(out[-7000:])
v.update(exit=int(re.search(r'Exit status: (\d+)',t)[1]),wall=re.search(r'Elapsed.*: (\S+)',t)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]),swaps=int(re.search(r'Swaps: (\d+)',t)[1]),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out),caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000))
if not v['axioms']:v['print_axioms']='N/A: unchanged SHA-frozen generated definitions; new laws audited in their consumer'
(E/f'receipt-{a}.json').write_text(json.dumps(v,indent=2)+'\n')
q=transport(['scp','-q',str(E/f'receipt-{a}.json'),f'{host}:{H}/evidence/receipt-{a}.json']);assert q.returncode==0,q.stderr
print({k:v[k] for k in ['attempt','target','exit','wall','peak_rss_kib','swaps']});sys.exit(v['exit'])
