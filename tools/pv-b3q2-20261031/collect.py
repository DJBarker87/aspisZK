from pathlib import Path
import subprocess
D=Path('evidence/pv-b3q2-20261031/host');D.mkdir(exist_ok=True)
H='/home/dombarker/project-offloads/codex-pv-b3q2-20261031/'
subprocess.run(['rsync','-a','--prune-empty-dirs','--include=/*/','--include=/*/receipt/','--include=/*/receipt/***','--include=/*/source.lean','--include=/*/target.json','--include=/*/reservation*','--include=/*/barrier.json','--include=/*/refusal.json','--include=/*/scope.log','--include=/preflight.json','--include=/cache-verification.json','--exclude=*','dombarker@100.108.41.90:'+H,str(D)+'/'],check=True)
