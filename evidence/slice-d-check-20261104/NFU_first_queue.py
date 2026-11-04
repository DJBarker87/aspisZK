from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
for i,target,invert in [(2,'r1_wire::NFU_wire::row_contract',True),(3,'r1_wire::NFU_wire::framed_identity',False),(4,'r1_wire::NFU_wire::framed_identity',True),(5,'r1_wire::NFU_wire::payload_identity',False),(6,'r1_wire::NFU_wire::payload_identity',True),(7,'compact::NFU_compact::check_one',False),(8,'compact::NFU_compact::check_one',True)]:
 env=dict(os.environ)
 if invert:env['NFU_INVERT']='1'
 a=f'NFU_K{i:03}'
 r=subprocess.run([sys.executable,str(E/'NFU_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('No receipt: '+r.stdout+r.stderr)
 rc=json.loads(p.read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if rc['exit_status']!=int(invert):raise SystemExit('Unexpected verdict; inspect '+a)
