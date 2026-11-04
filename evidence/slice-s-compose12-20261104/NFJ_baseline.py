"""Run inherited validators unchanged; write only our checked snapshot."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
sys.path.insert(0,str(E.parent/'slice-s-compose11-20261104'))
import NFH_validate as v
b=v.inherited.compose(v.inherited.baseline(),v.inherited.read(v.inherited.E/'NFD_LEDGER_DELTA.json'))
v.packet_check(json.loads((v.E/'NFH_LEDGER_DELTA.json').read_text()));v.artifacts()
(E/'NFJ_BASELINE.json').write_text(json.dumps(b,indent=1)+'\n')
print('Inherited baseline replayed',len(b['rows']))
