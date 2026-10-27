"""Serial receipt wrapper for the unchanged shared env-J launcher; no infrastructure edits."""
from pathlib import Path
import json,subprocess,sys,hashlib,re,shlex,time
E=Path(__file__).resolve().parent; R=E.parents[1]
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads'; D=B+'/codex-pv-inv-20261027'; J=D+'/inv2'; T=D+'/inv2-receipts'
def remote(c):return subprocess.run(['ssh',H,c],text=True,capture_output=True)
def save(p,s):p.write_text(s)
tally=json.loads((E/'TALLY.json').read_text());a=tally['next_env_j_id'];mod=sys.argv[1];assert mod.startswith('R1Z/PV_Inv_') and 43600<=a<=43899 and tally['lean_charged']<100
assert (tally['lean_charged']<97 and a<43897) or ('Audit' in mod and a>=43897)
p=R/'docs/research/v8-r0-zk-20261009/lean'/(mod+'.lean');src=p.read_text();q=E/f'J{a}';q.mkdir();save(q/'source.lean',src)
tally['next_env_j_id']=a+1;save(E/'TALLY.json',json.dumps(tally,indent=2)+'\n')
r=remote(f'python3 {B}/codex-cx-s2x-20261023/S2X_reservation.py {D}/reservation-{a}.json > {D}/reservation-{a}.log 2>&1; cat {D}/reservation-{a}.log; cat {D}/reservation-{a}.json')
save(q/'admission.log',r.stdout+r.stderr)
ad=remote(f'cat {D}/reservation-{a}.json');save(q/'admission.json',ad.stdout)
try:allowed=json.loads(ad.stdout)['allowed']
except Exception:print(r.stdout+r.stderr);sys.exit(79)
if not allowed:save(q/'refusal.json',json.dumps(dict(charged=False,reason='reservation refusal',exit=r.returncode)));print('REFUSED',a);sys.exit(78)
r=remote(f'mkdir -p {J}/sources/R1Z {J}/objects/R1Z {T}; test ! -e {T}/out-{a}.log');assert r.returncode==0,'ID exists on host'
subprocess.run(['scp','-q',str(p),H+':'+J+'/sources/'+mod+'.lean'],check=True)
imports=re.findall(r'^import (.+)$',src,re.M);depcode='''import json,pathlib,hashlib
E=json.load(open("'''+B+'''/r1-privacy-build-integration-20261019/env/J.json")); ps=[pathlib.Path("'''+J+'''/objects")]+[pathlib.Path(p) for p in E['LEAN_PATH'].split(':')]; ds=[]
for m in '''+repr([m for line in imports for m in line.split()])+''':
 p=next((p/(m.replace('.','/')+'.olean') for p in ps if (p/(m.replace('.','/')+'.olean')).exists()),None)
 ds.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p else 'missing'))
print(json.dumps(ds))
'''
deps=remote('python3 -c '+shlex.quote(depcode));save(q/'deps.json',deps.stdout);assert deps.returncode==0,deps.stderr
fp=hashlib.sha256(deps.stdout.encode()).hexdigest();cmd=f'systemd-run --user --scope --quiet -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 /usr/bin/time -v -o {T}/time-{a}.log timeout 900 python3 {B}/aspis-fs-generic-20261006/evidence/run2.py {B}/r1-privacy-build-integration-20261019/env/J.json {J}/objects {J}/sources {J}/objects/{mod}.olean {J}/sources/{mod}.lean 7000 > {T}/out-{a}.log 2>&1'
remote(f'sha256sum {J}/sources/{mod}.lean > {T}/sha-{a}.txt');
for old in E.glob('J*/receipt.json'):
 d=json.loads(old.read_text());assert (d['source_sha256'],d['deps_fingerprint'])!=(hashlib.sha256(src.encode()).hexdigest(),fp),'unchanged input refused'
started=time.monotonic();r=remote(cmd);save(q/'launcher.log',r.stdout+r.stderr)
for name,host in [('out.log',f'{T}/out-{a}.log'),('time.log',f'{T}/time-{a}.log'),('sha.log',f'{T}/sha-{a}.txt')]:
 z=remote('cat '+host);save(q/name,z.stdout+z.stderr)
o=(q/'out.log').read_text();t=(q/'time.log').read_text()
def val(p):
 m=re.search(p,t);return m[1].strip() if m else None
charged='Elapsed (wall clock)' in t
if charged:tally['lean_charged']+=1
save(E/'TALLY.json',json.dumps(tally,indent=2)+'\n')
ax=[' '.join(s.split()) for s in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",o,re.M|re.S)]
rec=dict(attempt=a,module=mod,charged=charged,command=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(src.encode()).hexdigest(),deps_fingerprint=fp,exit=int(val(r'Exit status:\s*(\d+)') or -1),outer_exit=r.returncode,wall=val(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),total_wall_seconds=time.monotonic()-started,peak_rss_kib=val(r'Maximum resident set size \(kbytes\):\s*(\d+)'),swaps=val(r'Swaps:\s*(\d+)'),axioms=ax,errors=[l for l in o.splitlines() if 'error:' in l],caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,LeanM=7000))
save(q/'receipt.json',json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2));print(o[-4500:]);sys.exit(rec['exit'] if rec['exit']>=0 else 1)
