"""Retain extracted std Option/Result, keep the ill-typed shift helper opaque."""
from pathlib import Path
import json
B=Path(__file__).resolve().parent;x=json.loads((B/'charon-005.json').read_text());cmd=x['command'];i=cmd.index('--dest-file');cmd[i:i]=['--include','core::option::_::ok_or','--include','core::result::_::clone']
x.update(attempt='charon-008',command=cmd,change='Retain successful std Option/Result inclusion; exclude final_len Usize→U32 shift mismatch (lean039), checkpoint_size stays explicit',deps_fingerprint={'scope':'same shipped owned callers, transitive widths and reached Option/Result bodies; checkpoint_size remains opaque'})
(B/'charon-008.json').write_text(json.dumps(x,indent=2)+'\n')
x=json.loads((B/'aeneas-004.json').read_text());x.update(attempt='aeneas-007',change='Keep ill-typed shift helper opaque; retain extracted std Option/Result bodies');x['command'][x['command'].index('-dest')+1]=str(B/'generated-final');(B/'aeneas-007.json').write_text(json.dumps(x,indent=2)+'\n')
