from pathlib import Path
import hashlib,json
from NDL_sources import source
E=Path(__file__).resolve().parent
src={n:source(n) for n in ['NDL_weights.rs','NDL_reference.rs']}
patch=''
for n,s in src.items():
 lines=s.splitlines(True);patch+='--- /dev/null\n+++ b/'+n+'\n@@ -0,0 +1,'+str(len(lines))+' @@\n'+''.join('+'+l for l in lines)
(E/'NDL_HARNESS_INPUTS.patch').write_text(patch)
(E/'NDL_HARNESS_INPUTS.json').write_text(json.dumps({n:hashlib.sha256(s.encode()).hexdigest() for n,s in src.items()},indent=2)+'\n')
