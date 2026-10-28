from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
# Explicitly run independent stages sequentially; never two scopes in this job.
for script in ['NCG_batch6.py','NCG_batch7.py','NCG_tail_batch.py']:
 r=subprocess.run([sys.executable,str(E/script)])
 if r.returncode:raise SystemExit(r.returncode)
