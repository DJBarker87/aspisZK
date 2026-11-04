from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K099','kani','verifier::NGC_windows::resize_step_u8'],env=env,capture_output=True,text=True);(E/'NGC_K099-local.log').write_text(r.stdout+r.stderr);print('NGC_K099',r.returncode,flush=True)
log=(E/'NGC_K099/stdout.log').read_text()
if 'timed out' in log or r.returncode!=0:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K100','kani','verifier::NGC_windows::resize_step_u8'],env=env,capture_output=True,text=True);(E/'NGC_K100-local.log').write_text(r.stdout+r.stderr);print('NGC_K100',r.returncode,flush=True)
log=(E/'NGC_K100/stdout.log').read_text()
if 'timed out' in log or r.returncode!=1:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K031','kani','verifier::NGC_windows::resize_step_q'],env=env,capture_output=True,text=True);(E/'NGC_K031-local.log').write_text(r.stdout+r.stderr);print('NGC_K031',r.returncode,flush=True)
log=(E/'NGC_K031/stdout.log').read_text()
if 'timed out' in log or r.returncode!=0:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K032','kani','verifier::NGC_windows::resize_step_q'],env=env,capture_output=True,text=True);(E/'NGC_K032-local.log').write_text(r.stdout+r.stderr);print('NGC_K032',r.returncode,flush=True)
log=(E/'NGC_K032/stdout.log').read_text()
if 'timed out' in log or r.returncode!=1:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K033','kani','verifier::NGC_windows::resize_step_raw'],env=env,capture_output=True,text=True);(E/'NGC_K033-local.log').write_text(r.stdout+r.stderr);print('NGC_K033',r.returncode,flush=True)
log=(E/'NGC_K033/stdout.log').read_text()
if 'timed out' in log or r.returncode!=0:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K034','kani','verifier::NGC_windows::resize_step_raw'],env=env,capture_output=True,text=True);(E/'NGC_K034-local.log').write_text(r.stdout+r.stderr);print('NGC_K034',r.returncode,flush=True)
log=(E/'NGC_K034/stdout.log').read_text()
if 'timed out' in log or r.returncode!=1:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K035','kani','verifier::NGC_windows::resize_step_wide'],env=env,capture_output=True,text=True);(E/'NGC_K035-local.log').write_text(r.stdout+r.stderr);print('NGC_K035',r.returncode,flush=True)
log=(E/'NGC_K035/stdout.log').read_text()
if 'timed out' in log or r.returncode!=0:raise SystemExit('Stop family on timeout/unexpected verdict')
env=os.environ.copy();env.pop('NGC_INVERT',None)
env['NGC_INVERT']='1'
r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K067','kani','verifier::NGC_windows::resize_step_wide'],env=env,capture_output=True,text=True);(E/'NGC_K067-local.log').write_text(r.stdout+r.stderr);print('NGC_K067',r.returncode,flush=True)
log=(E/'NGC_K067/stdout.log').read_text()
if 'timed out' in log or r.returncode!=1:raise SystemExit('Stop family on timeout/unexpected verdict')
