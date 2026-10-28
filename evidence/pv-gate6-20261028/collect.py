from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
D='/home/dombarker/project-offloads/codex-pv-gate6-20261028/'
# Keep receipt metadata and textual outputs; never copy binaries, keys, target or source trees.
subprocess.run(['rsync','-a','--prune-empty-dirs','--exclude=source','--exclude=native-target','--exclude=sbf-target*/','--exclude=artifacts/','--exclude=diagnostics/','--exclude=bin/','--exclude=ledger/','--exclude=*keypair*','--exclude=*.bin','--exclude=*.so','--exclude=__pycache__/','--include=*/','--include=*.json','--include=*.jsonl','--include=*.log','--include=*.txt','--include=*.py','--include=*.sh','--exclude=*','dombarker@100.108.41.90:'+D,str(E)+'/'],check=True)
