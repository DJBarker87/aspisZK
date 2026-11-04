from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,target,invert in [(58,'zero_result_window',False),(59,'zero_result_window',True),(60,'zero_pointer_window',False)]:
 env=dict(os.environ,NFQ_PROGRAM='1')
 if invert:env['NFQ_INVERT']='1'
 with (E/f'NFQ_K{n:03}-queue.log').open('w') as f:r=subprocess.run(['python3',str(E/'NFQ_run.py'),f'NFQ_K{n:03}','kani','r1_pool_adapter::NFQ_program::'+target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(n,r.returncode,flush=True)
 assert r.returncode==(1 if invert else 0)
