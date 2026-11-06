from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
# Continue only after prior serial queue is terminal; no parallel host scopes.
assert (E/'NJY_K024/receipt.json').is_file()
for n,f in [(25,'entry'),(29,'registry')]:
 for d,m in enumerate(['positive','inverse','unimplied','modifies']):
  subprocess.run([sys.executable,str(E/'NJY_shapes.py'),f'NJY_K{n+d:03}',f,m],check=True)
# Fixed source-order stages, native ONE loop step only. Controls follow a pass.
n=33
for f,ks in [('checkpoint',['length','head','digest_arg','digest_map','step','constructor']),('master',['length','head','identity_arg','policy_arg','identity_map','policy_map','step','constructor'])]:
 for k in ks:
  subprocess.run([sys.executable,str(E/'NJY_forest_segments.py'),f'NJY_K{n:03}',f,k,'positive'],check=True)
  r=json.loads((E/f'NJY_K{n:03}/receipt.json').read_text())
  if r['exit_status']==0:subprocess.run([sys.executable,str(E/'NJY_forest_segments.py'),f'NJY_K{n+1:03}',f,k,'inverse'],check=True)
  n+=2

for n,f in [(61,'checkpoint'),(65,'master')]:
 for d,m in enumerate(['positive','inverse','unimplied','modifies']):
  subprocess.run([sys.executable,str(E/'NJY_forest_shapes.py'),f'NJY_K{n+d:03}',f,m],check=True)
