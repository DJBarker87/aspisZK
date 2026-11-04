"""Run one proof-work command with the standing admission and resource caps.

This uses, without changing, the existing reservation/barrier tools.
"""
from pathlib import Path
import hashlib, json, re, shlex, subprocess, sys, time, os
R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-uc5-20261103'
D='/home/dombarker/project-offloads/codex-pv-uc-20261029'
H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name,phase,source=sys.argv[1:]
p=R/source
assert subprocess.check_output(['git','show','HEAD:'+source],cwd=R)==p.read_bytes()
source_sha=hashlib.sha256(p.read_bytes()).hexdigest()
module=source.split('/lean/',1)[1][:-5].replace('/','.')
assert len(list(E.glob('lean*/receipt.json')))<100
cmd=['python3',D+'/lean-one-uc5.py',name[4:],module,source_sha]
source_revision_at_launch=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
for f in E.glob('**/admission-*.json'):
 try:
  a=json.loads(f.read_text())
  if a.get('allowed') is False:
   import datetime
   deadline=datetime.datetime.fromisoformat(a['utc']).timestamp()+180
   while time.time()<deadline: time.sleep(min(30,deadline-time.time()))
 except (KeyError,ValueError): pass

assert re.fullmatch(r'lean910[0-9]{2}',name) and cmd
out=E/name
assert not out.exists(), 'ID directory already exists: never reuse an ID; reconcile it first'
out.mkdir()
runner_sources=['tools/pv-uc5-20261103/lean-one.py','tools/pv-uc-20261029/authority-preflight.py']
inputs={source:source_sha,**{f:hashlib.sha256((R/f).read_bytes()).hexdigest() for f in runner_sources}}
(out/'source-inputs.json').write_text(json.dumps(dict(revision=source_revision_at_launch,files=inputs,dirty=subprocess.check_output(['git','status','--porcelain'],cwd=R,text=True)),indent=2)+'\n')
def ssh(c,retry=True):
 if os.environ.get('PV_C474_QUIET_OWNER')=='1':
  assert name.startswith('native751') and cmd[-1]==D+'/bundle/timing.py'
  check="import json,time; x=json.load(open('/home/dombarker/project-offloads/QUIET_WINDOW.json')); assert x['owner']=='pv-c474-20261029' and time.time()<x['until']"
  c='python3 -c '+shlex.quote(check)+' && export QUIET_WINDOW_OWNER=1 && '+c
 for attempt in range(1,11):
  q=subprocess.run(['ssh',H,c],text=True,capture_output=True)
  if q.returncode!=255 or not retry:return q
  with (out/'transport.jsonl').open('a') as f:
   f.write(json.dumps(dict(command=c,exit=255,try_number=attempt,compiler_launch=False))+'\n')
  if attempt<10:
   print('SSH 255 before launch/read-only recovery; waiting 60s',flush=True);time.sleep(60)
 return q
r=ssh(f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission-before.json > {D}/{name}/reservation.log 2>&1')
for f in ['admission-before.json','reservation.log']:
 q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout+q.stderr)
ad=json.loads((out/'admission-before.json').read_text())
if r.returncode!=0 or ad.get('allowed') is not True:
 print('UNCHARGED REFUSAL',r.returncode,{k:ad.get(k) for k in ['utc','allowed','error','bounded_reserved_bytes','safe_limit_bytes']});sys.exit(78)
# Correctly stage this job's committed inputs only AFTER recorded admission.
# Shared runners, sources and authoritative objects are never written here.
staging=[]
for local,remote in [(source,D+'/lean/'+module.replace('.','/')+'.lean'),*[(f,D+('/lean-one-uc5.py' if Path(f).name=='lean-one.py' else '/'+Path(f).name)) for f in runner_sources]]:
 assert subprocess.check_output(['git','show','HEAD:'+local],cwd=R)==(R/local).read_bytes()
 q=ssh('mkdir -p '+shlex.quote(str(Path(remote).parent)));assert q.returncode==0,q.stderr
 for attempt in range(10):
  q=subprocess.run(['scp',str(R/local),H+':'+remote],capture_output=True,text=True)
  if q.returncode!=255:break
  with (out/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(stage='own committed input staging before Lean launch',exit=255,try_number=attempt+1))+'\n')
  if attempt<9:time.sleep(60)
 assert q.returncode==0,q.stderr
 q=ssh('sha256sum '+shlex.quote(remote));assert q.returncode==0 and q.stdout.split()[0]==inputs[local],q.stdout+q.stderr
 staging.append(dict(source=local,host_path=remote,sha256=inputs[local]))
(out/'staged-inputs.json').write_text(json.dumps(staging,indent=2)+'\n')
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',G+'/barrier.py',D+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',D+'/'+name+'/time.log',*cmd]
admit=f'python3 {G}/reservation.py {D}/{name}/admission-launch.json > {D}/{name}/reservation-launch.log 2>&1'
check='python3 -c '+shlex.quote("import json; assert json.load(open("+repr(D+'/'+name+'/admission-launch.json')+"))['allowed'] is True")
launch=admit+' && '+check+' && '+shlex.join(run)+f' > {D}/{name}/output.log 2>&1'
if True:
 # Long arithmetic gate: detach once, then one short read-only SSH at a time.
 # A lost submission response never causes a second launch.
 done=D+'/'+name+'/done-status.txt'
 body=launch+'; result=$?; printf "%s\\n" "$result" > '+shlex.quote(done)
 detached='nohup sh -c '+shlex.quote(body)+f' > {D}/{name}/detached.log 2>&1 < /dev/null &'
 r=ssh(detached,retry=False)
 if r.returncode not in (0,255):raise SystemExit(r.returncode)
 while True:
  q=ssh('if test -f '+shlex.quote(done)+'; then cat '+shlex.quote(done)+'; else tail -1 '+shlex.quote(D+'/'+name+'/output.log')+' 2>/dev/null; exit 1; fi')
  if q.returncode==0:
   r.returncode=int(q.stdout.strip());break
  if q.returncode!=1:raise SystemExit(q.returncode)
  print(q.stdout.strip() or 'Scope admitted; awaiting completion',flush=True)
  time.sleep(10)
else:
 r=ssh(launch,retry=False)
if r.returncode==255:
 with (out/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(stage='after scope submission; NOT resubmitted',exit=255))+'\n')
 print('SSH 255 after scope submission; waiting 60s then collecting read-only',flush=True);time.sleep(60)
for f in ['admission-launch.json','reservation-launch.log','admission-barrier.json','output.log','time.log']:
 q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout+q.stderr)
launch=json.loads((out/'admission-launch.json').read_text())
if launch.get('allowed') is not True:
 print('UNCHARGED LAUNCH REFUSAL',launch.get('utc'));sys.exit(78)
bar=json.loads((out/'admission-barrier.json').read_text())
if bar.get('allowed') is not True:
 print('UNCHARGED BARRIER REFUSAL',{k:bar.get(k) for k in ['utc','allowed','error','bounded_reserved_bytes','safe_limit_bytes']});sys.exit(78)
tim=(out/'time.log').read_text()
def field(s):
 m=re.search(s+r':\s*(.+)',tim);return m[1] if m else None
actual_exit=field('Exit status')
actual_exit=int(actual_exit) if actual_exit is not None else r.returncode
receipt=dict(target=run,exit=actual_exit,transport_exit=r.returncode,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),source_revision=source_revision_at_launch,expected_phase=phase,print_axioms='Compilation only; new top theorem axioms must be audited separately',source_sha256=source_sha,module=module,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
log=(out/'output.log').read_text()
results=[json.loads(line[len('LEAN_RESULT '):]) for line in log.splitlines() if line.startswith('LEAN_RESULT ')]
if results:
 assert len(results)==1
 receipt['elaboration_result']=results[0]
receipt['source_git_blob']=subprocess.check_output(['git','rev-parse',source_revision_at_launch+':'+source],cwd=R,text=True).strip()
receipt['print_axioms_lines']=[' '.join(s.split()) for s in re.findall(r"^('[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms))",log,re.M|re.S)]
if receipt['print_axioms_lines']:receipt['print_axioms']=receipt['print_axioms_lines']
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
# Full admission inventories stay on the host; retain decisions and a byte hash.
for f in ['admission-before.json','admission-launch.json','admission-barrier.json']:
 raw=(out/f).read_bytes();a=json.loads(raw)
 (out/f).write_text(json.dumps(dict(sha256=hashlib.sha256(raw).hexdigest(),host_path=D+'/'+name+'/'+f,**{k:a.get(k) for k in ['allowed','utc','error','bounded_reserved_bytes','safe_limit_bytes']}),indent=2)+'\n')
print((out/'output.log').read_text()[-5000:]);print(json.dumps(receipt))
sys.exit(actual_exit)
