"""Invoke the existing admitted env-J runner on one private source."""
from pathlib import Path
import subprocess,json,hashlib,shlex,re,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';H='/home/dombarker/project-offloads/codex-pv-2tnv-20261028';host='dombarker@100.108.41.90'
a=int(sys.argv[1]);m=sys.argv[2];s=R/sys.argv[3];assert 60900<=a<=60999
assert not (E/f'receipt-{a}.json').exists()
def ssh(c):return subprocess.run(['ssh',host,c],capture_output=True,text=True)
# Refusals return immediately; caller observes cooldown and retries same ID.
c=f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {H}/reservation-{a}.json > {H}/reservation-{a}.log 2>&1\nrc=$?\ncat {H}/reservation-{a}.log\nexit $rc'
r=ssh(c);(E/f'reservation-{a}.log').write_text(r.stdout+r.stderr)
assert r.returncode!=255,'transport before launch: retry under ruling p'
try:ad=json.loads(r.stdout.strip().splitlines()[-1])
except Exception:raise RuntimeError(r.stdout+r.stderr)
if r.returncode or not ad['allowed']:print(r.stdout);sys.exit(78)
# Cross-job ID collision check, including private receipt filenames.
code="""from pathlib import Path
import re,json
n=NUMBER;root=Path('/home/dombarker/project-offloads');hits=[]
for job in root.glob('codex-pv-*'):
 if job.name=='codex-pv-2tnv-20261028':continue
 for p in job.glob('**/*NUMBER*'):
  if p.is_file() and re.search(r'(^|[-_])NUMBER([-_.]|$)',p.name):hits.append(str(p))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt'
lines=[l for l in sent.read_text().splitlines() if re.search(r'\\bNUMBER\\b',l)]
print(json.dumps(dict(hits=hits,sent=lines)))
""".replace('NUMBER',str(a))
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
idcheck=json.loads(r.stdout);(E/f'id-{a}.json').write_text(json.dumps(idcheck,indent=2)+'\n');assert not idcheck['hits'] and not idcheck['sent'],idcheck
# Source path is private; shared sources/objects are never modified.
subprocess.run(['scp','-q',str(s),host+':'+H+'/sources/'+m+'.lean'],check=True)
code=f'''from pathlib import Path
import json,hashlib,re
h=Path({H!r});e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));e['LEAN_PATH']=str(h/'objects')+':/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin16-lean/std-cache:'+e['LEAN_PATH'];(h/'J.json').write_text(json.dumps(e));roots=[Path(x) for x in e['LEAN_PATH'].split(':')];out={{}}
for imp in re.findall(r'^import\\s+(\\S+)',(h/'sources'/{(m+'.lean')!r}).read_text(),re.M):
 rel=imp.replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).is_file()),None);out[imp]=dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest()) if p else None
print(json.dumps(out))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr;deps=json.loads(r.stdout);assert all(deps.values()),deps
sha=hashlib.sha256(s.read_bytes()).hexdigest();fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
for p in E.glob('receipt-*.json'):
 old=json.load(open(p));assert (old['source_sha256'],old['deps_fingerprint'])!=(sha,fp),'unchanged rerun'
cmd=['systemd-run','--user','--scope','--quiet','--unit=pv-2tnv-'+str(a),'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',H+f'/time-{a}.log','timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',H+'/J.json',H+'/objects',H+'/sources',H+'/objects/'+m+'.olean',H+'/sources/'+m+'.lean','7000']
record=dict(attempt=a,target=m,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=sha,source_path=str(s.relative_to(R)),deps_fingerprint=fp,dependencies=deps,admission=ad,command=cmd)
(E/f'launch-{a}.json').write_text(json.dumps(record,indent=2)+'\n')
print('LAUNCH',a,m,flush=True);t=time.monotonic();r=ssh(shlex.join(cmd)+f' > {H}/out-{a}.log 2>&1');record['launcher_exit']=r.returncode;record['wall_seconds']=time.monotonic()-t
assert r.returncode!=255,'submitted: recover receipts read-only; do not resubmit'
for name in ['out','time']:
 q=ssh('cat '+H+f'/{name}-{a}.log');assert q.returncode==0,q.stderr;(E/f'{name}-{a}.log').write_text(q.stdout)
out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
for key,pat in [('exit',r'Exit status: (\d+)'),('peak_rss_kib',r'Maximum resident set size \(kbytes\): (\d+)'),('swaps',r'Swaps: (\d+)')]:
 match=re.search(pat,tim);record[key]=int(match[1]) if match else None
record['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
record['accepted']=r.returncode==0 and record['exit']==0 and 'error:' not in out and 'sorryAx' not in out
(E/f'receipt-{a}.json').write_text(json.dumps(record,indent=2)+'\n');print(out[-2500:]);print(json.dumps({k:record[k] for k in ['attempt','exit','wall_seconds','peak_rss_kib','swaps','accepted']}));sys.exit(0 if record['accepted'] else 1)
