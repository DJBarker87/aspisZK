from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1])
for mode in ['value','allocation','argument','reply']:
 a=f'NEX_K{n:03}';n+=1;assert n<=141
 subprocess.run([sys.executable,str(E/'NEX_prepare_late.py'),mode],check=True);(E/(a+'-shape.json')).write_bytes((E/'NEX_LATE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEX_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::NEX_late::late'],capture_output=True,text=True)
 print(a,mode,r.stdout[-1100:],r.stderr,flush=True);log=(E/a/'stdout.log').read_text()
 if 'VERIFICATION:- SUCCESSFUL' in log or 'Failed Checks:' not in log:raise SystemExit('excluded or unexpected; inspect')
