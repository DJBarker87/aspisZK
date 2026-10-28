from pathlib import Path
import sys
from NCX_run import launch
E=Path(__file__).resolve().parent
a,target=sys.argv[1:]
f='NCX_generated/'+target.replace('.','/')+'.lean'
files={f:(Path('lean')/(target.replace('.','/')+'.lean')).read_text()}
r=launch(a,'lean',target.replace('.','/'),files,['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NCX_generated','-o','NCX_objects/'+target.replace('.','/')+'.olean',f],[f])

sys.exit(0 if r["exit_status"]==0 else 1)
