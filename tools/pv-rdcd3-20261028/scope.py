"""Serial capped proof/native launch using the standing admission tools."""
from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028';D='/home/dombarker/project-offloads/codex-pv-rdcd3-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name,phase,*cmd=sys.argv[1:];assert re.fullmatch(r'[A-Za-z0-9_-]+',name) and cmd
# A refusal imposes a job-wide180s cooldown, even if later host admission would allow.
from datetime import datetime,timezone
refusals=[]
launch_clock=E/"last-launch.json"
if launch_clock.exists():
 refusals.append(json.loads(launch_clock.read_text())["epoch"])
for history in list(E.glob('*/admission-history.jsonl'))+list(E.glob('*/barrier-history.jsonl')):
 for line in history.read_text().splitlines():
  entry=json.loads(line);admission=entry.get('admission',{})
  if admission.get('allowed') is False and admission.get('utc'):
   refusals.append(datetime.fromisoformat(admission['utc']).timestamp())
if refusals:
 remaining=180-(datetime.now(timezone.utc).timestamp()-max(refusals))
 if remaining>0:
  print(f'LOCAL COOLDOWN: wait at least{remaining:.1f}s; no host launch',flush=True)
  sys.exit(78)
out=E/name;out.mkdir(exist_ok=True);assert not (out/'receipt.json').exists()
def ssh(c):
 for k in range(11):
  r=subprocess.run(['ssh',H,c],text=True,capture_output=True)
  if r.returncode!=255:return r
  (out/f'transport-{time.time_ns()}.log').write_text(r.stdout+r.stderr)
  if k==10:raise RuntimeError('persistent transport failure')
  time.sleep(60)
prior=ssh(f'test ! -f {D}/{name}/time.log')
if prior.returncode!=0:raise RuntimeError('Host time.log already exists: recover read-only, never resubmit')
def collect(names):
 code='import pathlib,json; d=pathlib.Path('+repr(D+'/'+name)+'); print(json.dumps({n:(d/n).read_text() if (d/n).exists() else "" for n in '+repr(names)+'}))'
 q=ssh(shlex.join(['python3','-c',code]))
 if q.returncode:raise RuntimeError('Read-only collection failed; never resubmit an existing target')
 for filename,data in json.loads(q.stdout).items():(out/filename).write_text(data)
for k in range(11):
 r=ssh(f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission-before.json > {D}/{name}/reservation.log 2>&1')
 collect(['admission-before.json','reservation.log'])
 ad=json.loads((out/'admission-before.json').read_text())
 with (out/'admission-history.jsonl').open('a') as hist:hist.write(json.dumps(dict(exit=r.returncode,admission=ad))+'\n')
 if ad.get('error'):
  race=bool(re.search(r'\[Errno (?:2|19)\]',ad['error']))
  history=[json.loads(x) for x in (out/'admission-history.jsonl').read_text().splitlines()]
  consecutive=0
  for item in reversed(history):
   if re.search(r'\[Errno (?:2|19)\]',item.get('admission',{}).get('error','')):consecutive+=1
   else:break
  print('Admission error:',ad['error'],flush=True)
  if race and consecutive<4:sys.exit(79)
  sys.exit(70)
 if r.returncode==0 and ad.get('allowed') is True:break
 (out/f'refusal-{k}.json').write_text(json.dumps(dict(exit=r.returncode,admission=ad)))
 if k==10:sys.exit(78)
 print('UNCHARGED admission refusal; wait at least180s and retry the SAME unlaunched ID under (m′)',flush=True);sys.exit(78)
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',G+'/barrier.py',D+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',D+'/'+name+'/time.log',*cmd]
# Submission is never automatically repeated after a transport loss.
launch_clock.write_text(json.dumps(dict(epoch=time.time(),target=name))+"\n")
r=subprocess.run(['ssh',H,shlex.join(run)+f' > {D}/{name}/output.log 2>&1'],text=True,capture_output=True)
if r.returncode==255:
 (out/'submission-transport.log').write_text(r.stderr);time.sleep(60)
 for k in range(15):
  q=ssh(f'test -f {D}/{name}/time.log && tail -1 {D}/{name}/time.log')
  if q.returncode==0 and 'Exit status:' in q.stdout:break
  time.sleep(60)
 else:raise RuntimeError('submitted result unresolved; do not rerun')
 status=int(q.stdout.split(':')[-1])
else:status=r.returncode
collect(['admission-barrier.json','output.log','time.log'])
bar=json.loads((out/'admission-barrier.json').read_text())
with (out/'barrier-history.jsonl').open('a') as hist:hist.write(json.dumps(dict(exit=status,admission=bar))+'\n')
if bar.get('allowed') is not True:
 print('UNCHARGED barrier refusal',bar.get('error',''),flush=True)
 if bar.get('error'):
  history=[json.loads(x) for x in (out/'barrier-history.jsonl').read_text().splitlines()];consecutive=0
  for item in reversed(history):
   if re.search(r'\[Errno (?:2|19)\]',item.get('admission',{}).get('error','')):consecutive+=1
   else:break
  if re.search(r'\[Errno (?:2|19)\]',bar['error']) and consecutive<4:sys.exit(79)
  sys.exit(70)
 sys.exit(78)
tim=(out/'time.log').read_text();log=(out/'output.log').read_text()
def field(s):
 m=re.search(s+r':\s*(.+)',tim);return m[1] if m else None
receipt=dict(target=run,exit=status,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),expected_phase=phase,axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S) if phase=='Lean' else 'N/A native configuration/body audit',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(log[-6000:]);print(json.dumps({k:receipt[k] for k in ['exit','wall','peak_rss_kib','swap']}));sys.exit(status)
