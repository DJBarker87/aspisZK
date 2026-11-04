"""Only this job's environment, and the ax1' standalone NEP_Driver runtime."""
import os,sys,json
from pathlib import Path
env=json.loads(Path(sys.argv[1]).read_text())
for k,v in env.items():
 if v is None:os.environ.pop(k,None)
 else:os.environ[k]=v
os.chdir(Path(sys.argv[1]).parent/'evidence')
lean=env['LEAN']
os.execv(lean,[lean,'-j1','-M7000','-DElab.async=false','--run',sys.argv[2],'pv-stx'])
