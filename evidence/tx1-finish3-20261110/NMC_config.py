from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
attempt,module=sys.argv[1:3]
x=dict(attempt=attempt,kind="lean",module=module,sources=["NMC_generated/"+module+".lean"],command=["/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake","env","lean","-j1","-M7000","-DElab.async=false","-R","NMC_generated","-o","NMC_objects/"+module+".olean","NMC_generated/"+module+".lean"],env=json.loads((E/"NMC_ENV.json").read_text()),timeout=180,collect=[])
(E/(attempt+".json")).write_text(json.dumps(x))
