from pathlib import Path
import os,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit30-20261022')
lane=int(sys.argv[1]);assert lane in [0,1]
os.environ.update(PROVER_KANI_LANE=str(lane),KANI_OBJECT_BITS='12',KANI_UNWINDSET='memcmp.0:40')
for row in range(lane,25,2):
 if row in [14,15]:continue
 target=f'sim::caller_kani30::row{row:02}'
 print('Starting',target,flush=True)
 subprocess.run(['python3',str(H/'harness/kani.py'),f'caller30-row{row:02}-context-v1',target],check=True)
