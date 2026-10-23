from pathlib import Path
import json
B=Path(__file__).resolve().parent;x=json.loads((B/'charon-006.json').read_text());cmd=x['command'];i=cmd.index('--dest-file');cmd[i:i]=['--include','aspis_r1_cost_probe::transport::_::folds']
x.update(attempt='charon-007',command=cmd,change='Include final_len transitive folds enum method, no shipped source change',deps_fingerprint={'scope':'same production source and checkpoint_size; transitive folds enum body included'})
(B/'charon-007.json').write_text(json.dumps(x,indent=2)+'\n')
x=json.loads((B/'aeneas-005.json').read_text());x.update(attempt='aeneas-006',change='Include transitive folds enum method');x['command'][x['command'].index('-dest')+1]=str(B/'generated-v6');(B/'aeneas-006.json').write_text(json.dumps(x,indent=2)+'\n')
