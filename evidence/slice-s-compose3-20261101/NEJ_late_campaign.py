from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,(case,mode) in enumerate([(s,m) for s in range(5) for m in ['positive','negative']],40):
 a=f'NEJ_K{n:03}'
 subprocess.run([sys.executable,str(E/'NEJ_prepare_late_step.py'),str(case),mode],check=True)
 (E/(a+'-window.json')).write_bytes((E/'NEJ_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEJ_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::NEJ_late_step::header_window'],capture_output=True,text=True);print(r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved launch')
 log=(E/a/'stdout.log').read_text()
 if ('VERIFICATION:- SUCCESSFUL' in log)!=(mode=='positive') or 'timed out' in log.lower() or (mode=='negative' and 'Failed Checks:' not in log):raise SystemExit('OPEN native window/control: inspect and split')
