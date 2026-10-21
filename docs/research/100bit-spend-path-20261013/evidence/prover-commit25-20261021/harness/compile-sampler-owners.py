from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent.parent
rows=json.loads((E/'sampler-owners.json').read_text())
for attempt,row in enumerate(rows[int(sys.argv[1]):],int(sys.argv[2])):
 module=row['module']
 print(f'J{attempt}: {module}',flush=True)
 subprocess.run([sys.executable,str(E/'harness/lean.py'),module,str(attempt)],check=True)
 out=subprocess.check_output(['ssh','dombarker@100.108.41.90',f'cat /home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/out-{attempt}.log'],text=True)
 if '\nexit=0\n' not in '\n'+out:raise SystemExit(f'Focused failure J{attempt}; stop before dependents')
