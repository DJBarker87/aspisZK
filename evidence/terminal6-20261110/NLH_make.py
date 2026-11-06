"""Private configuration writer; unchanged admitted host launcher."""
from pathlib import Path
import json,sys
p=Path(__file__).resolve().parent
attempt,module=sys.argv[1:3]
x=dict(attempt=attempt,kind='lean',module=module,sources=[module+'.lean','NLH_seed.py','NLH_SEED_INPUTS.json'],command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NLH_objects/'+module+'.olean',module+'.lean'],timeout=180,expected_time='Focused symbolic source-order composition; compilation, not arithmetic normalization',env=json.loads((p/'NLH_ENV.json').read_text()))
(p/(attempt+'.json')).write_text(json.dumps(x))
