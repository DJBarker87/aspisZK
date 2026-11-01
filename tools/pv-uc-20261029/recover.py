"""Read-only receipt recovery for an already submitted native scope. Never launches."""
from pathlib import Path
import subprocess,json,re,sys,hashlib,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029';D='/home/dombarker/project-offloads/codex-pv-uc-20261029';H='dombarker@100.108.41.90'
name=sys.argv[1];assert re.fullmatch(r'native751[0-9]{2}',name);O=E/name;assert O.is_dir()
if (O/'receipt.json').is_file():print('Receipt already present; do not overwrite');raise SystemExit(0)
def ssh(command):
 for i in range(10):
  r=subprocess.run(['ssh',H,command],capture_output=True)
  if r.returncode!=255:return r
  with (O/'recovery-transport.jsonl').open('a') as f:f.write(json.dumps(dict(exit=255,try_number=i+1,stage='read-only recovery; never resubmitted'))+'\n')
  if i<9:time.sleep(60)
 raise RuntimeError('persistent SSH failure; scope NOT resubmitted')
r=ssh('cat '+D+'/'+name+'/done-status.txt')
if r.returncode:print('PENDING: no done status; do not resubmit or launch another own scope');raise SystemExit(75)
status=int(r.stdout.strip());pending=json.loads((O/'pending-status.json').read_text());source=json.loads((O/'source-inputs.json').read_text())
for f in ['admission-before.json','admission-launch.json','admission-barrier.json','reservation.log','reservation-launch.log','output.log','time.log']:
 r=ssh('cat '+D+'/'+name+'/'+f);assert r.returncode==0,(f,r.stderr)
 if f.startswith('admission-'):
  a=json.loads(r.stdout);assert a['allowed'] is True
  (O/f).write_text(json.dumps(dict(sha256=hashlib.sha256(r.stdout).hexdigest(),host_path=D+'/'+name+'/'+f,**{k:a.get(k) for k in ['allowed','utc','error','bounded_reserved_bytes','safe_limit_bytes']}),indent=2)+'\n')
 else:(O/f).write_bytes(r.stdout)
t=(O/'time.log').read_text()
def field(pattern):
 m=re.search(pattern+r':\s*(.+)',t);assert m,pattern;return m[1]
actual=int(field('Exit status'));assert actual==status
receipt=dict(target=pending['command'],exit=actual,transport_exit=status,wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\)'),swap=field('Swaps'),source_revision=source['revision'],expected_phase='final-1000-pair-differential',print_axioms='N/A native/extraction; Lean results separately audited',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),recovered_read_only=True)
(O/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
