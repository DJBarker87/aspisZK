from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
a,module=sys.argv[1:3]
x=dict(attempt=a,kind="lean",module=module,sources=["NLU_generated/"+module+".lean"],command=["/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake","env","lean","-j1","-M7000","-DElab.async=false","-R","NLU_generated","-o","NLU_objects/"+module+".olean","NLU_generated/"+module+".lean"],env=json.loads((E/"NLU_ENV.json").read_text()),timeout=180,collect=[])
(E/(a+".json")).write_text(json.dumps(x))
