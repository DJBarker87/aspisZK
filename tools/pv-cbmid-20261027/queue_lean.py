"""Serial focused-target queue; resource refusals wait, theorem errors stop."""
from pathlib import Path
import subprocess,json,sys,time,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cbmid-20261027'
modules=sys.argv[1:];assert modules
for module in modules:
 refusals=0
 while True:
  state=out/'admission-state.json'
  if state.exists():
   remaining=json.loads(state.read_text()).get('retry_after',0)-time.time()
   if remaining>0:
    print(f'WAIT {module}: {remaining:.0f}s until next permitted admission',flush=True)
    time.sleep(min(remaining+0.1,60));continue
  tally=json.loads((out/'TALLY.json').read_text())
  if len(tally['lean_charged'])>=97 or tally['next_id']>=40897:
   print('RESERVED AUDIT BUDGET: stopping ordinary queue',flush=True);sys.exit(77)
  result=subprocess.run([sys.executable,str(root/'tools/pv-cbmid-20261027/lean.py'),module],cwd=root)
  if result.returncode==0:break
  if result.returncode!=78:sys.exit(result.returncode)
  refusals+=1
  if refusals>=10:
   print('TEN ADMISSION REFUSALS: return to compile-free preparation before resuming',flush=True);sys.exit(78)
print('QUEUE COMPLETE',flush=True)
