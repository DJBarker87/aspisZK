from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K096','kani','verifier::NGC_windows::fill_push_u8'],env=env,capture_output=True,text=True);(E/'NGC_K096-local.log').write_text(r.stdout+r.stderr);print('NGC_K096',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K097','kani','verifier::NGC_windows::fill_push_u8'],env=env,capture_output=True,text=True);(E/'NGC_K097-local.log').write_text(r.stdout+r.stderr);print('NGC_K097',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K098','kani','verifier::NGC_windows::fill_push_q'],env=env,capture_output=True,text=True);(E/'NGC_K098-local.log').write_text(r.stdout+r.stderr);print('NGC_K098',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K099','kani','verifier::NGC_windows::fill_push_q'],env=env,capture_output=True,text=True);(E/'NGC_K099-local.log').write_text(r.stdout+r.stderr);print('NGC_K099',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K100','kani','verifier::NGC_windows::fill_push_raw'],env=env,capture_output=True,text=True);(E/'NGC_K100-local.log').write_text(r.stdout+r.stderr);print('NGC_K100',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K031','kani','verifier::NGC_windows::fill_push_raw'],env=env,capture_output=True,text=True);(E/'NGC_K031-local.log').write_text(r.stdout+r.stderr);print('NGC_K031',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K032','kani','verifier::NGC_windows::fill_push_wide'],env=env,capture_output=True,text=True);(E/'NGC_K032-local.log').write_text(r.stdout+r.stderr);print('NGC_K032',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K033','kani','verifier::NGC_windows::fill_push_wide'],env=env,capture_output=True,text=True);(E/'NGC_K033-local.log').write_text(r.stdout+r.stderr);print('NGC_K033',r.returncode,flush=True)
if r.returncode not in [0,1] or 'timed out' in r.stdout or 'timed out' in r.stderr:raise SystemExit('Stop on timeout; split before any further family member')
