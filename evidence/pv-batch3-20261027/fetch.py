from pathlib import Path
import subprocess,sys
D=Path(__file__).resolve().parent/'receipts';D.mkdir(exist_ok=True)
H='dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-batch3-20261027/'
for label in sys.argv[1:]:
 subprocess.run(['rsync','-a','--include=*/','--include=*.json','--include=*.log','--exclude=artifacts/***','--exclude=diagnostics/***','--exclude=*',H+label+'/',str(D/label)+'/'],check=True)
