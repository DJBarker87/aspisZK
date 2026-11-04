from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
for i,h,invert in [(6,'powers29_step',True),(7,'powers7_step',False),(8,'powers7_step',True)]:
 env=dict(os.environ)
 if invert:env['NFW_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_K{i:03}','kani','weights::NFW_weights::'+h],env=env,capture_output=True,text=True)
 (E/f'NFW_K{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,r.returncode,r.stdout[:450],flush=True)
 if r.returncode!=int(invert):sys.exit(r.returncode or 2)
for i,n in [(9,'NFW_PowersFrame'),(10,'NFW_PrepareInspect')]:
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_L{i:03}','lean',n],capture_output=True,text=True)
 (E/f'NFW_L{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,r.returncode,r.stdout[-2500:],flush=True)
 if r.returncode:sys.exit(r.returncode)
