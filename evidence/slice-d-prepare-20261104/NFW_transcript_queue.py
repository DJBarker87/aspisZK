from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
for i,h,invert in [(10,'copy_digest',True),(11,'new_seed',False),(12,'new_seed',True),(13,'absorb_window',False),(14,'absorb_window',True),(15,'block_window',False),(16,'block_window',True)]:
 env=dict(os.environ)
 if invert:env['NFW_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_K{i:03}','kani','transcript::NFW_transcript::'+h],env=env,capture_output=True,text=True)
 (E/f'NFW_K{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,r.returncode,r.stdout[:350],flush=True)
 if r.returncode!=int(invert):sys.exit(r.returncode or 2)
