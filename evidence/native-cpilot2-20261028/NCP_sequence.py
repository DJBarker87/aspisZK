from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
names=['slice_weak_check','slice_real','slice_stub','slice_frame_check','slice_frame_real','vec_inverted_check','vec_weak_check','vec_real','vec_stub','vec_frame_check','vec_frame_real']
for i,n in enumerate(names,2):
 r=subprocess.run(['python3',str(E/'NCP_run.py'),f'NCP_K{i:03}',f'NCP_controls::NCP_{n}'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(f'NCP_K{i:03}',n,r.returncode,r.stdout[-1500:],flush=True)
 if r.returncode not in [0,1]:break
 if 'Traceback' in r.stdout or 'STOP' in r.stdout:break
