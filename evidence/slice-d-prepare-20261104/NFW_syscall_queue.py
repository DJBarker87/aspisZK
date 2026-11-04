from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
for i,h,flag in [(18,'copy_hash','NFW_INVERT'),(19,'syscall_bytes',None),(20,'syscall_bytes','NFW_INVERT'),(21,'syscall_bytes','NFW_BADARG')]:
 env=dict(os.environ,NFW_PROGRAM='1')
 if flag:env[flag]='1'
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_K{i:03}','kani','NFW_syscall::'+h],env=env,capture_output=True,text=True)
 (E/f'NFW_K{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,r.returncode,r.stdout[:350],flush=True)
 if r.returncode!=int(bool(flag)):sys.exit(r.returncode or 2)
