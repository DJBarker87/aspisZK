from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;shape=sys.argv[1];n=int(sys.argv[2])
for mode in ['native','contract','unimplied','inverted','frame']:
 a=f'NEL_K{n:03}';n+=1;subprocess.run([sys.executable,str(E/'NEL_prepare_result_shape.py'),shape,mode],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NEL_RESULT_SHAPE_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEL_kani_run.py'),a,'kani','pool_v1::payment_relation::NEL_result_shape::shape_control'],capture_output=True,text=True);print(a,mode,r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch')
 log=(E/a/'stdout.log').read_text();want=mode in ['native','contract']
 if ('VERIFICATION:- SUCCESSFUL' in log)!=want or 'timed out' in log.lower() or (not want and 'Failed Checks:' not in log):raise SystemExit('STOP inspect fidelity finding/input')
