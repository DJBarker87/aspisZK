from pathlib import Path
import subprocess,json,sys
E=Path('evidence/pv-extract-20261027');rows=json.loads((E/'field-bridges.json').read_text())
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for row in rows[start:]:
 t=json.loads((E/'TALLY.json').read_text());n=t['next_env_j_id']
 if t['lean_charged']>=58:print('Reserve final two for audit/manifest');break
 subprocess.run([sys.executable,'tools/pv-extract-20261027/lean.py',str(n),row['module']],check=True)
 p=E/f'{n}.json'
 if not p.exists() or json.loads(p.read_text())['exit']!=0:print('STOP',row['module'],flush=True);break
