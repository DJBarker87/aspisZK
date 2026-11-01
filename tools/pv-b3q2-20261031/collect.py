from pathlib import Path
import subprocess
D=Path('evidence/pv-b3q2-20261031/host');D.mkdir(exist_ok=True)
H='/home/dombarker/project-offloads/codex-pv-b3q2-20261031/'
subprocess.run(['rsync','-a','--prune-empty-dirs','--include=/*/','--include=/*/receipt/','--include=/*/receipt/***','--include=/*/source.lean','--include=/*/target.json','--include=/*/reservation*','--include=/*/barrier.json','--include=/*/refusal.json','--include=/*/scope.log','--include=/*/quiet-window.json','--include=/preflight.json','--include=/cache-verification.json','--include=/preaudit-verification.json','--include=/direct-source-staging*.json','--include=/direct-feature-association.json','--include=/direct*-cone-extraction-input.json','--include=/direct3.stdout','--include=/direct3.stderr','--include=/direct-metadata.stderr','--exclude=*','dombarker@100.108.41.90:'+H,str(D)+'/'],check=True)
