#!/usr/bin/env python3
"""One focused proof check through the lead's existing launcher; collect receipts."""
import atexit, datetime, hashlib, json, pathlib, re, shlex, subprocess, sys, time
root=pathlib.Path(__file__).resolve().parents[2]
e=root/'evidence/pv-runjoin12-20261027'
atexit.register(lambda: subprocess.run([sys.executable,str(root/'tools/pv-runjoin12-20261027/tally.py')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL))
flag=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
assert flag.is_file(), 'host rebuild gate closed'
assert 'HOST RESTORED' in flag.read_text()
attempt=int(sys.argv[1]); module=sys.argv[2]
assert 40900<=attempt<=41199
assert not (e/f'used-{attempt}.json').exists(), 'ID already consumed'
(e/f'used-{attempt}.json').write_text(json.dumps(dict(attempt=attempt,module=module,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
charged=sum(json.loads(p.read_text()).get('exit') is not None for p in e.glob('receipt-*.json'))
assert charged<100, 'Lean budget exhausted'
assert charged<97 or 'TrustAudit12' in module, 'Final three charged attempts reserved for focused trust audit'
source=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean')
if len(sys.argv)>3:source=root/sys.argv[3]
assert source.is_file(), source
host='dombarker@100.108.41.90'; job='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
joint='/home/dombarker/project-offloads/aspis-joint-20261019'
launcher='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
def ssh(command):return subprocess.run(['ssh','-o','BatchMode=yes',host,command],capture_output=True,text=True)
# Reservation output is retained on the host before any scp.
reservation=f'{job}/evidence/runjoin12-reservation-{attempt}'
r=ssh(f'python3 {job}/reservation-existing.py {reservation}.json > {reservation}.log 2>&1\ncat {reservation}.log')
(e/f'reservation-{attempt}.log').write_text(r.stdout+r.stderr)
try: admission=json.loads(r.stdout.strip().splitlines()[-1])
except Exception:
 print('RESERVATION RECEIPT MISSING: '+r.stdout+r.stderr,flush=True);sys.exit(79)
if not admission.get('allowed'):
 (e/f'refusal-{attempt}.json').write_text(json.dumps(admission,indent=2)+'\n')
 print('RESERVATION REFUSED: '+json.dumps(admission),flush=True);sys.exit(78)
for suffix in ['json','log']:
 subprocess.run(['scp','-q',f'{host}:{reservation}.{suffix}',str(e/f'reservation-{attempt}.{suffix}')],check=True)
# Save any previous shared source/object before this worker's source changes.
backup=f'{job}/runjoin12-shared-backups/{attempt}'
code=f'''import pathlib,shutil
b=pathlib.Path({backup!r});b.mkdir(parents=True,exist_ok=True)
for kind,suffix in [('sources','.lean'),('objects','.olean'),('objects','.ir')]:
 p=pathlib.Path({joint!r})/kind/({module!r}+suffix)
 if p.exists():
  dest=b/kind/({module!r}+suffix);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
p=pathlib.Path({joint!r})/'sources'/({module!r}+'.lean');p.parent.mkdir(parents=True,exist_ok=True)
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
subprocess.run(['scp','-q',str(source),f'{host}:{joint}/sources/{module}.lean'],check=True)
sha=hashlib.sha256(source.read_bytes()).hexdigest()
snapshot=f'{attempt}-{source.name}.txt';(e/snapshot).write_bytes(source.read_bytes())
code=f'''import pathlib,json,re,hashlib
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')); roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];p=pathlib.Path({joint!r})/'sources'/({module!r}+'.lean'); d={{}}
for m in re.findall(r'^import\\s+(\\S+)',p.read_text(),re.M):
 rel=pathlib.Path(*m.split('.')).with_suffix('.olean');q=next((r/rel for r in roots if (r/rel).is_file()),None);d[m]=dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()) if q else None
print(json.dumps(dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),imports=d, fingerprint=hashlib.sha256(json.dumps(d,sort_keys=True).encode()).hexdigest())))
'''
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr
deps=json.loads(r.stdout);assert deps['source_sha256']==sha
command=[launcher,str(attempt),module,'J','7000','8',deps['fingerprint']]
launcher_source=ssh('cat '+launcher)
assert launcher_source.returncode==0,launcher_source.stderr
active_lines='\n'.join(x for x in launcher_source.stdout.splitlines() if not x.lstrip().startswith('#'))
tasks=int(re.findall(r'TasksMax=(\d+)',active_lines)[-1])
launcher_pin=hashlib.sha256(launcher_source.stdout.encode()).hexdigest()
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
record=dict(attempt=attempt,target=module,source_revision=revision,source_sha256=sha,source_snapshot=snapshot,
 dependencies=deps['imports'],deps_fingerprint=deps['fingerprint'],command=command,reservation=admission,
 limits=dict(lean_memory_mb=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=tasks),launcher_sha256=launcher_pin,
 source_was_uncommitted=(subprocess.run(['git','show','HEAD:'+str(source.relative_to(root))],cwd=root,capture_output=True).stdout != source.read_bytes()),shared_backup=backup,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
with (e/'launches.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
print('LAUNCH '+str(attempt)+' '+module,flush=True)
started=time.monotonic();r=ssh(shlex.join(command));record['launcher_wall_seconds']=time.monotonic()-started
(e/f'launcher-{attempt}.log').write_text(r.stdout+r.stderr)
print(r.stdout+r.stderr,flush=True)
record['launcher_exit']=r.returncode
for name in ['out','time','sha']:
 rr=ssh(f'cat {T}/{name}-{attempt}.'+('txt' if name=='sha' else 'log'))
 (e/f'{name}-{attempt}.{ "txt" if name=="sha" else "log" }').write_text(rr.stdout+rr.stderr)
out=(e/f'out-{attempt}.log').read_text();tim=(e/f'time-{attempt}.log').read_text()
m=re.findall(r'^exit=(\d+)',out,re.M);record['exit']=int(m[-1]) if m else None
m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim);record['peak_rss_bytes']=int(m[1])*1024 if m else None
m=re.search(r'Swaps: (\d+)',tim);record['swaps']=int(m[1]) if m else None
m=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',tim)
if m:
 v=m[1].split(':');record['wall_seconds']=sum(float(x)*60**i for i,x in enumerate(reversed(v)))
record['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out)
record['accepted']=record['exit']==0 and 'error:' not in out and 'sorryAx' not in out
(e/f'receipt-{attempt}.json').write_text(json.dumps(record,indent=2)+'\n')
if record['accepted']:
 r=ssh('mkdir -p '+job+'/lean-objects/'+str(pathlib.Path(module).parent)+'; cp '+joint+'/objects/'+module+'.olean '+job+'/lean-objects/'+module+'.olean'); assert r.returncode==0,r.stderr
print('RECEIPT '+json.dumps({k:record.get(k) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','accepted']}),flush=True)
sys.exit(0 if record['accepted'] else 1)
