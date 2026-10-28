"""Submit one new PV_L2D module through the unchanged shared env-J launcher."""
from pathlib import Path
import json, subprocess, shlex, hashlib, re, sys, datetime, time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
H='/home/dombarker/project-offloads/codex-pv-l2d-20261028';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);m=sys.argv[2];assert 51500<=a<=51599 and m.startswith('PV_L2D_')
assert not (E/f'receipt-{a}.json').exists()
s=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
b=s.read_bytes();sha=hashlib.sha256(b).hexdigest();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert subprocess.check_output(['git','show',rev+':'+str(s.relative_to(R))])==b
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', b.decode())
# Correct ruling m': refusals stay on the same unlaunched ID after 180s.
for p in E.glob('refusal-*.json'):
 age=time.time()-json.loads(p.read_text())['epoch']
 assert age>=180, f'cooldown {180-age:.1f}s remains; no launch'
def transport(args):
 for retry in range(11):
  q=subprocess.run(args,text=True,capture_output=True)
  if q.returncode!=255:return q
  with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,stderr=q.stderr))+'\n')
  if retry==10:raise RuntimeError('ten SSH retries exhausted')
  time.sleep(60)
def ssh(code):return transport(['ssh',host,code])
code='''import pathlib,re,json
r=pathlib.Path('/home/dombarker/project-offloads');pat=re.compile(r'(?<![A-Za-z0-9])ID(?![A-Za-z0-9])');hits=[]
for d in r.glob('codex-pv-*'):
 if d.name=='codex-pv-l2d-20261028':continue
 for p in d.glob('**/*ID*'):
  if p.is_file() and pat.search(p.name):hits.append(str(p))
sent=r/'r1-privacy-build-integration-20261019/evidence/sent.txt'
print(json.dumps(dict(other_receipts=hits,sent_hits=[l for l in sent.read_text().splitlines() if len(l.split())>2 and l.split()[2]=='ID'])))
'''.replace('ID',str(a))
q=ssh('python3 -c '+shlex.quote(code));assert q.returncode==0,q.stderr
v=json.loads(q.stdout);(E/f'id-audit-{a}.json').write_text(json.dumps(v,indent=2)+'\n');assert not v['other_receipts'] and not v['sent_hits'],v
q=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/admission-{a}.json > {H}/admission-{a}.log 2>&1\npv_status=$?\ncat {H}/admission-{a}.log\nexit $pv_status')
(E/f'admission-{a}.log').write_text(q.stdout+q.stderr)
admission=json.loads(q.stdout.strip().splitlines()[-1]);admission['epoch']=time.time()
if q.returncode!=0 or not admission['allowed']:
 (E/f'refusal-{a}.json').write_text(json.dumps(admission,indent=2)+'\n');print('REFUSED',admission);sys.exit(78)
q=transport(['scp','-q',str(s),host+':/home/dombarker/project-offloads/aspis-joint-20261019/sources/'+m+'.lean']);assert q.returncode==0,q.stderr
q=transport(['scp','-q',f'{host}:{H}/admission-{a}.json',str(E/f'admission-{a}.json')]);assert q.returncode==0,q.stderr
fp='pv-l2d-h4-'+hashlib.sha256((E/'external-authority.json').read_bytes()).hexdigest()[:16]
cmd=f'/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh {a} {m} J 7000 8 {fp}'
# Never transport-retry a submitted compile; recover logs read-only if link fails.
q=subprocess.run(['ssh',host,cmd],text=True,capture_output=True)
(E/f'launcher-{a}.log').write_text(q.stdout+q.stderr);print(q.stdout[-6500:]+q.stderr,flush=True)
if q.returncode in [65,78] and 'exit=' not in q.stdout:
 (E/f'refusal-{a}.json').write_text(json.dumps(dict(epoch=time.time(),allowed=False,launcher_exit=q.returncode,output=q.stdout),indent=2)+'\n');sys.exit(q.returncode)
for kind in ['out','time','sha']:
 suf='.txt' if kind=='sha' else '.log'
 c=ssh(f'cat /home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/{kind}-{a}{suf}');assert c.returncode==0,c.stderr
 (E/f'{kind}-{a}{suf}').write_text(c.stdout)
t=(E/f'time-{a}.log').read_text();out=(E/f'out-{a}.log').read_text()
v=dict(attempt=a,target=m,source_revision=rev,source_path=str(s.relative_to(R)),source_blob=subprocess.check_output(['git','rev-parse',rev+':'+str(s.relative_to(R))],text=True).strip(),source_sha256=sha,exit=int(re.search(r'Exit status: (\d+)',t)[1]),wall=re.search(r'Elapsed.*: (\S+)',t)[1],peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]),swaps=int(re.search(r'Swaps: (\d+)',t)[1]),axioms=re.findall(r"'PV_[^\n]+",out),external_preflight='external-preflight.json',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000),command=cmd)
(E/f'receipt-{a}.json').write_text(json.dumps(v,indent=2)+'\n')
sys.exit(v['exit'])
