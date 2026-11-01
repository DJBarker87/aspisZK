from pathlib import Path
import subprocess,json,time,datetime,sys
E=Path(__file__).resolve().parent;R='/home/dombarker/project-offloads/codex-pv-k3scan-20261101';INF='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';HOST='dombarker@100.108.41.90'
not_before=datetime.datetime.fromisoformat('2026-11-01T22:57:53.514897+00:00').timestamp()+180
records=[]
for attempt in range(3,11):
 while time.time()<not_before:time.sleep(min(30,not_before-time.time()))
 log=R+f'/control-upload-admission-{attempt}.log';receipt=R+f'/control-upload-admission-{attempt}.json'
 cmd=f'python3 {INF}/reservation.py {receipt} > {log} 2>&1; code=$?; cat {log}; exit $code'
 r=subprocess.run(['ssh',HOST,cmd],text=True,capture_output=True)
 rec={'attempt':attempt,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr};records.append(rec);(E/'control-queue.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(rec),flush=True)
 if r.returncode==255:
  # No scope has been submitted at this point. Keep transport failures distinct.
  not_before=time.time()+60;continue
 try:a=json.loads(r.stdout)
 except Exception:not_before=time.time()+180;continue
 if r.returncode or not a.get('allowed'):
  not_before=time.time()+180;continue
 uploaded=subprocess.run(['scp',str(E/'run_host.py'),str(E/'control_worker.py'),HOST+':'+R+'/'])
 if uploaded.returncode:raise SystemExit(uploaded.returncode)
 rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
 launch=subprocess.run(['ssh',HOST,f'PV_SOURCE_REVISION={rev} python3 {R}/run_host.py K79201 negative'],text=True,capture_output=True)
 rec['launch']={'exit':launch.returncode,'stdout':launch.stdout,'stderr':launch.stderr};(E/'control-queue.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(rec['launch']),flush=True)
 # Exit 1 is expected if and only if retained output identifies the matched assertion.
 if launch.returncode==78:not_before=time.time()+180;continue
 if launch.returncode==255:
  print('Transport failed after submission; recover read-only, never resubmit',flush=True)
 raise SystemExit(0)
raise SystemExit('Admission retries exhausted; no control launched')
