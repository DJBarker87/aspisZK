from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parent
raise SystemExit(subprocess.run([sys.executable,str(R/"check_llbc_targets.py")]).returncode)
