"""Retry admission only; every actual computation is delegated unchanged to run.py."""
from pathlib import Path
import json,sys,subprocess,time
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cbmid-20261027'
mode,stem,*args=sys.argv[1:];refused=0
while refused<10:
 state=out/'admission-state.json'
 if state.exists():
  left=json.loads(state.read_text()).get('retry_after',0)-time.time()
  if left>0:
   print(f'WAIT {stem}: {left:.0f}s until next permitted admission',flush=True)
   time.sleep(min(left+.1,60));continue
 name=stem if refused==0 else f'{stem}-admit{refused+1:02}'
 if (out/name/'receipt.json').exists():
  old=json.loads((out/name/'receipt.json').read_text());assert old.get('compiler_started') is False
  refused+=1;continue
 result=subprocess.run([sys.executable,str(root/'tools/pv-cbmid-20261027/run.py'),mode,name,*args],cwd=root)
 if result.returncode!=78:sys.exit(result.returncode)
 refused+=1
print('TEN ADMISSION REFUSALS: perform compile-free preparation before resuming',flush=True)
sys.exit(78)
