from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,f,m in [(2,'entry','inverse'),(3,'entry','unimplied'),(4,'entry','modifies'),(5,'registry','positive'),(6,'registry','inverse'),(7,'registry','unimplied'),(8,'registry','modifies')]:
 if m!='positive':
  a='NJY_K001' if f=='entry' else 'NJY_K005'
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
 r=subprocess.run([sys.executable,str(E/'NJY_shapes.py'),f'NJY_K{n:03}',f,m]);assert r.returncode==0
