from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,f in [(61,'checkpoint'),(65,'master')]:
 for d,m in enumerate(['positive','inverse','unimplied','modifies']):
  if (E/f'NJY_K{n+d:03}/receipt.json').exists():continue
  subprocess.run([sys.executable,str(E/'NJY_forest_shapes.py'),f'NJY_K{n+d:03}',f,m],check=True)
for n,f,k in [(69,'checkpoint','step'),(71,'checkpoint','loop_window'),(73,'master','loop_window')]:
 subprocess.run([sys.executable,str(E/'NJY_forest_segments.py'),f'NJY_K{n:03}',f,k,'positive'],check=True)
 if json.loads((E/f'NJY_K{n:03}/receipt.json').read_text())['exit_status']==0:subprocess.run([sys.executable,str(E/'NJY_forest_segments.py'),f'NJY_K{n+1:03}',f,k,'inverse'],check=True)
