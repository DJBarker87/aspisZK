#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib,sys
B=Path(__file__).resolve().parents[3];E=B/'evidence/stage2-continuation-20261020';raw=(E/'generated/AspisR1Stage2/Types.lean').read_text()
s=re.sub(r'(?m)^import AspisR1Stage2.TypesExternal\n|^set_option max(?:Heartbeats|RecDepth) .*\n','',raw)
p=B/'lean/Stage2ContinuationTypes.lean'
if '--check' in sys.argv:
 norm=lambda t:re.sub(r'\s+',' ',re.sub(r'/\-[\s\S]*?\-/','',t))
 assert norm(p.read_text())==norm(s),'used generated type definitions changed'
else:p.write_text(s)
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
(E/'proofs/types-binding.json').write_text(json.dumps(dict(generated_sha256=sha(raw),adapter_sha256=sha(p.read_text()),scope='Whole emitted type declarations; removed only unused TypesExternal import and emitter limit settings; comments ignored in --check'),indent=2)+'\n')
