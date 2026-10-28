# Run one independent Lean repair after the current native attempt terminates.
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
assert not (E/'NCO_ACTIVE.json').exists()
subprocess.run([sys.executable,str(E/'NCO_run.py'),'NCO_L004','lean','NCO_ScalarBridge'],check=True)
