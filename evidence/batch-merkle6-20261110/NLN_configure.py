"""Create an owned single-module configuration; never launches a scope."""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
number,module=sys.argv[1:];a='NLN_L'+number.zfill(3)
x=json.loads((E/'NLN_L001.json').read_text())
x.update(attempt=a,module=module,sources=[module+'.lean'],upload=[module+'.lean'],command=[x['command'][0],'env','lean','-j1','-M7000','-DElab.async=false','-o','NLN_objects/'+module+'.olean',module+'.lean'])
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
