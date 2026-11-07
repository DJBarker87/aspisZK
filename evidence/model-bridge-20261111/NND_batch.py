"""Serial own-module batch; every member still gets its own admission/receipt."""
from NND_formal import run
import sys
start=int(sys.argv[1])
for i,n in enumerate(sys.argv[2:],start):
 r=run(f'NND_L{i:03}','lean',n)
 if r['exit_status']:raise SystemExit(r['exit_status'])
