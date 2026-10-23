from pathlib import Path
import json
H=Path(__file__).resolve().parent;x=json.loads((H/'charon-002.json').read_text());cmd=x['command'];i=cmd.index('--dest-file');extras=['--consts','values']
for name in ['aspis_statement::pool_v1::format::PoolV1FormatError','aspis_statement::pool_v1::verifier_registry::VerifierEntryStatusV1','crate::r1_pool_adapter::readonly_meta_ok','crate::r1_pool_adapter::readonly_buffer_meta_ok']:
 extras+=['--include',name]
cmd[i:i]=extras;x.update(attempt='charon-003',command=cmd,change='Include two formerly opaque enum layouts and small metadata children; evaluate literal constants to avoid unconstrained constant callbacks.')
(H/'charon-003.json').write_text(json.dumps(x,indent=2)+'\n')
