"""Run one proof-work command with the standing admission and resource caps.

This uses, without changing, the existing reservation/barrier tools.
"""
from pathlib import Path
import hashlib, json, re, shlex, subprocess, sys, time
R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-fxmem-20261028'
D='/home/dombarker/project-offloads/codex-pv-fxmem-20261028'
H='dombarker@100.108.41.90'
G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name,phase,*cmd=sys.argv[1:]
assert re.fullmatch(r'[a-zA-Z0-9_-]+',name) and cmd
out=E/name;out.mkdir(exist_ok=True)
assert not (out/'receipt.json').exists()
def ssh(c, retry=True):
 for attempt in range(1,11):
  r=subprocess.run(['ssh',H,c],text=True,capture_output=True)
  if r.returncode!=255:return r
  with (E/'transport.jsonl').open('a') as f:f.write(json.dumps(dict(operation=c,exit=255,error=r.stderr,attempt=attempt,read_or_precompiler=retry,epoch=time.time()))+'\n')
  if not retry or attempt==10:return r
  time.sleep(60)

r=ssh(f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission-before.json > {D}/{name}/reservation.log 2>&1')
for f in ['admission-before.json','reservation.log']:
 q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout+q.stderr)
ad=json.loads((out/'admission-before.json').read_text())
if r.returncode!=0 or ad.get('allowed') is not True:
 print('UNCHARGED REFUSAL',r.returncode,{k:ad.get(k) for k in ['utc','allowed','error','bounded_reserved_bytes','safe_limit_bytes']});sys.exit(78)
run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',G+'/barrier.py',D+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',D+'/'+name+'/time.log',*cmd]
r=ssh(shlex.join(run)+f' > {D}/{name}/output.log 2>&1',retry=False)
for f in ['admission-barrier.json','output.log','time.log']:
 q=ssh(f'cat {D}/{name}/{f}');(out/f).write_text(q.stdout+q.stderr)
bar=json.loads((out/'admission-barrier.json').read_text())
if bar.get('allowed') is not True:
 print('UNCHARGED BARRIER REFUSAL',{k:bar.get(k) for k in ['utc','allowed','error','bounded_reserved_bytes','safe_limit_bytes']});sys.exit(78)
tim=(out/'time.log').read_text()
def field(s):
 m=re.search(s+r':\s*(.+)',tim);return m[1] if m else None
actual_exit=field('Exit status')
status=int(actual_exit) if actual_exit is not None else r.returncode
receipt=dict(target=run,exit=status,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),expected_phase=phase,print_axioms='N/A native/extraction; Lean results separately audited',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print((out/'output.log').read_text()[-14000:]);print(json.dumps(receipt))
sys.exit(status)
