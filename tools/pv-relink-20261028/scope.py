"""Serial capped proof/native launch using the standing admission tools."""
from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name,phase,*cmd=sys.argv[1:];assert re.fullmatch(r'[A-Za-z0-9_-]+',name) and cmd
out=E/name;out.mkdir(exist_ok=True);assert not (out/'receipt.json').exists()
def ssh(c):
 for k in range(11):
  r=subprocess.run(['ssh',H,c],text=True,capture_output=True)
  if r.returncode!=255:return r
  (out/f'transport-{time.time_ns()}.log').write_text(r.stdout+r.stderr)
  if k==10:raise RuntimeError('persistent transport failure')
  time.sleep(60)
for k in range(11):
 r=ssh(f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission-before.json > {D}/{name}/reservation.log 2>&1')
 for f in ['admission-before.json','reservation.log']:
  q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout)
 ad=json.loads((out/'admission-before.json').read_text())
 if r.returncode==0 and ad.get('allowed') is True:break
 (out/f'refusal-{k}.json').write_text(json.dumps(dict(exit=r.returncode,admission=ad)))
 if k==10:sys.exit(78)
 print('admission refused; waiting three minutes',flush=True);time.sleep(180)
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',G+'/barrier.py',D+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',D+'/'+name+'/time.log',*cmd]
# Submission is never automatically repeated after a transport loss.
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
for f in ['admission-barrier.json','output.log','time.log']:
 q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout)
bar=json.loads((out/'admission-barrier.json').read_text())
if bar.get('allowed') is not True:print('UNCHARGED barrier refusal');sys.exit(78)
tim=(out/'time.log').read_text();log=(out/'output.log').read_text()
def field(s):
 m=re.search(s+r':\s*(.+)',tim);return m[1] if m else None
receipt=dict(target=run,exit=status,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),expected_phase=phase,axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S) if phase=='Lean' else 'N/A native finite validation',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(log[-6000:]);print(json.dumps({k:receipt[k] for k in ['exit','wall','peak_rss_kib','swap']}));sys.exit(status)
