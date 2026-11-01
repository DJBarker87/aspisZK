from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NEJ_relocate_oracle.py')],check=True)
plan=[('m31','positive'),('m31','negative'),('parts','positive'),('parts','negative'),('common','positive'),('common','negative')]
for n,(case,mode) in enumerate(plan,34):
 a=f'NEJ_K{n:03}'
 if case=='m31':
  subprocess.run([sys.executable,str(E/'NEJ_prepare_m31.py'),mode],check=True);h='pool_v1::pair_forest_terminal::NEJ_oracle::frame_m31'
 else:
  r=subprocess.run([sys.executable,str(E/'NEJ_prepare_frame.py'),case,mode],capture_output=True,text=True);assert r.returncode==0,r.stderr;h=r.stdout.strip()
 (E/(a+'-projection.json')).write_bytes((E/'NEJ_CONTRACT_ERASURE.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEJ_kani_run.py'),a,'kani',h],capture_output=True,text=True);print(r.stdout[-1300:],r.stderr,flush=True)
 if not (E/a/'receipt.json').exists():raise SystemExit('STOP unresolved native attempt')
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if rc['exit_status'] and 'Failed Checks:' not in log and 'timed out' not in log.lower():raise SystemExit('STOP own input/codegen error; repair')
