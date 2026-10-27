"""Collect text receipts, excluding keys, binaries, and raw fixture material."""
from pathlib import Path
import subprocess
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';E=Path('evidence/pv-batch2-20261027')
cmd="python3 - <<'PY2'\nfrom pathlib import Path\nD=Path('"+D+"')\nfor p in D.rglob('*'):\n if not p.is_file():continue\n r=p.relative_to(D)\n if any(x in r.parts for x in ['src','artifacts','diagnostics','bin','baseline-inputs','candidate-inputs','timing-precheck']):continue\n if p.name.endswith(('.json','.log','.txt')):print(r)\nPY2"
r=subprocess.run(['ssh',H,cmd],capture_output=True,text=True,check=True)
for line in r.stdout.splitlines():
 p=E/line;p.parent.mkdir(parents=True,exist_ok=True);subprocess.run(['scp','-q',H+':'+D+'/'+line,str(p)],check=True)
