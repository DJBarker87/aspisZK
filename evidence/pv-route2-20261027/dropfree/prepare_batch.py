# Prepare immutable per-root command packets without launching any scope.
from pathlib import Path
import os,subprocess,json
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027/dropfree');rows=[]
for op,suffix,source in [(134,'02','134.rs'),(36,'01','36-generic-ownership.rs'),(36,'02','36.rs'),(205,'01','205.rs'),(212,'01','212.rs'),(215,'01','215.rs'),(216,'01','216.rs'),(217,'01','217.rs'),(219,'01','219.rs'),(250,'01','250.rs')]:
 env=dict(os.environ,VARIANT=suffix,PROBE_SOURCE=source,PREPARE_ONLY='1')
 if not (D/f'phase-input-{op}-{suffix}'/'phases.json').exists():subprocess.run(['python3',str(D/'run_combined.py'),str(op)],env=env,check=True)
 for row in json.loads((D/f'phase-input-{op}-{suffix}'/'phases.json').read_text()):row['key']=f'{op}-{suffix}';row['phase']='charon' if Path(row['directory']).name.startswith('charon') else 'aeneas';rows.append(row)
P=D/'batch-missing-01';P.mkdir(exist_ok=True);(P/'phases.json').write_text(json.dumps(rows,indent=2))
