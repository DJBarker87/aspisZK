from pathlib import Path
import subprocess,json,sys
q=json.loads(Path('evidence/pv-batch2-20261027/constructor-field-queue.json').read_text())
which=sys.argv[1] if len(sys.argv)>1 else 'source'
mods=(['R1Z/PV_B2_WeightsNativeTypes'] if which=='source' else [])+q[which]
raise SystemExit(subprocess.run(['python3','tools/pv-batch2-20261027/queue.py',*mods]).returncode)
