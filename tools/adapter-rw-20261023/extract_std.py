"""Extract the tiny reached std/value methods rather than assume their outputs."""
from pathlib import Path
import json
B=Path(__file__).resolve().parent;x=json.loads((B/'charon-005.json').read_text());cmd=x['command'];i=cmd.index('--dest-file')
names=['core::option::_::ok_or','core::result::_::clone','aspis_r1_cost_probe::verifier::checkpoint_size','aspis_r1_cost_probe::transport::_::final_len','aspis_r1_cost_probe::verifier::CHECKPOINT_FIXED']
cmd[i:i]=[a for n in names for a in ['--include',n]]
x.update(attempt='charon-006',command=cmd,change='Extract reached Option::ok_or, Result::clone and checkpoint_size, no function source change',deps_fingerprint={'scope':'same production sources, tiny reached std and checkpoint-size bodies included'})
(B/'charon-006.json').write_text(json.dumps(x,indent=2)+'\n')
x=json.loads((B/'aeneas-004.json').read_text());x.update(attempt='aeneas-005',change='Expanded tiny std method inclusion; unchanged owned source');x['command'][x['command'].index('-dest')+1]=str(B/'generated-v5')
(B/'aeneas-005.json').write_text(json.dumps(x,indent=2)+'\n')
