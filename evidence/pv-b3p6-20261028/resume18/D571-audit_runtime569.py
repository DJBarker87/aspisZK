"""Run NEP standalone with the identical private compile environment."""
import os,sys,json
from pathlib import Path
env=json.loads(Path(sys.argv[1]).read_text())
for k,v in env.items():
 if v is None:os.environ.pop(k,None)
 else:os.environ[k]=v
objects,root,src,limit=sys.argv[2:6]
os.environ['LEAN_PATH']=objects+':'+os.environ['LEAN_PATH']
lean=env['LEAN']
os.execv(lean,[lean,'-j1','-M'+limit,'-DElab.async=false','-R',root,'--run',src])
