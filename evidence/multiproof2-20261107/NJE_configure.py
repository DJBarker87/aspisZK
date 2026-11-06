"""Create a focused compile configuration; does not launch builds."""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
attempt,module=sys.argv[1:3]
x=json.load(open(E/'NJE_L001.json'))
x.update(attempt=attempt,module=module,sources=['NJE_lean/'+module+'.lean'],upload=['NJE_lean/'+module+'.lean'],collect=[])
x['command']=[s.replace('NJE_ArityPackets',module) for s in x['command']]
(E/(attempt+'.json')).write_text(json.dumps(x,indent=2)+'\n')
print(attempt+' configured: '+module)
