"""Read-only evidence transfer, after explicit reservation admission."""
from pathlib import Path
import subprocess,json,sys
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch1-20261027';E=Path('evidence/pv-batch1-20261027')
label=sys.argv[1]
r=subprocess.run(['ssh',H,f'cd {D}; python3 Port13GATE_admission.py > reservation-{label}.json 2>&1 && cat reservation-{label}.json'],text=True,capture_output=True)
(E/f'admission-{label}.log').write_text(r.stdout+r.stderr)
assert r.returncode==0 and json.loads(r.stdout)['allowed'] is True,'transfer refused; wait three minutes'
subprocess.run(['rsync','-a','--include=build-*/','--include=receipt/','--include=*.json','--include=*.log','--exclude=*',H+':'+D+'/candidate/',str(E/'candidate')+'/'],check=True)
subprocess.run(['rsync','-a','--include=*.json','--include=*-launcher.log','--exclude=*',H+':'+D+'/',str(E)+'/'],check=True)
