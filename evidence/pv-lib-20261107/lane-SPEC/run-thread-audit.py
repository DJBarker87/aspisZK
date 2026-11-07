"""Existing standalone NEP invocation with task-local paths; fixed caps."""
import json,os,sys
from pathlib import Path
p=Path(sys.argv[1]);env=json.loads(p.read_text())
for key,value in env.items():
 if value is None:os.environ.pop(key,None)
 else:os.environ[key]=value
out=p.parent/'evidence'/'raw-audit';out.mkdir(exist_ok=True);os.chdir(out)
os.execv(env['LEAN'],[env['LEAN'],'-j1','-M7000','-DElab.async=false','--run',sys.argv[2],'pv-thread'])
