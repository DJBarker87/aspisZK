"""One unrolled native decoder field/control per admitted attempt."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);family=sys.argv[2]
jobs=json.loads(sys.argv[3]);assert family in ['afterdecode','snapshotdecode']
for slot,mode in jobs:
 a=f'NEX_K{n:03}';n+=1;assert n<=141
 subprocess.run([sys.executable,str(E/('NEX_prepare_'+family+'.py')),mode,str(slot)],check=True)
 current='NEX_'+('AFTERDECODE' if family=='afterdecode' else 'SNAPSHOTDECODE')+'_CURRENT.json'
 (E/(a+'-shape.json')).write_bytes((E/current).read_bytes())
 parent='pair_terminal' if family=='afterdecode' else 'pair_tree_profile'
 r=subprocess.run([sys.executable,str(E/'NEX_kani_run.py'),a,'kani','pool_v1::'+parent+'::NEX_'+family+'::'+family],capture_output=True,text=True)
 print(a,family,slot,mode,r.stdout[-1100:],r.stderr,flush=True)
 log=(E/a/'stdout.log').read_text()
 if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or (mode!='positive' and 'Failed Checks:' not in log):raise SystemExit('excluded or unexpected; inspect and split, never rerun unchanged')
