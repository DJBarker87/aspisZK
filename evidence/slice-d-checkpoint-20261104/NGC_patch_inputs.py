from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/lib.rs';x[n]='#![cfg_attr(kani,feature(allocator_api))]\n'+x[n];(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
