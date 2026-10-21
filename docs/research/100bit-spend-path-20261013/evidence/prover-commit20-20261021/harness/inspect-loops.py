from pathlib import Path
import subprocess,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit20-20261021')
files=list((H/'kani-contract-target/kani/x86_64-unknown-linux-gnu/debug/deps').glob('*empty_entry.out'));assert len(files)==1,files
cmd=['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--show-loops',str(files[0])]
subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts/table-loops-v1'),'Inspect CBMC loop IDs; no proof or arithmetic','--',*cmd],check=True)
