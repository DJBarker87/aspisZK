"""Expose transitively referenced constant initializers, never opaque numerals."""
from pathlib import Path
import json,re
B=Path(__file__).resolve().parent
x=json.loads((B/'charon-004.json').read_text());cmd=x['command'];i=cmd.index('--dest-file')
consts=['aspis_r1_cost_probe::compact::'+n for n in re.findall(r'^pub const (\w+)',(B/'src/crates/aspis-r1-cost-probe/src/compact.rs').read_text(),re.M)]
consts += ['aspis_r1_cost_probe::verifier::SEMANTIC_BYTES','aspis_statement::pool_v1::pair_terminal::POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES','aspis_statement::pool_v1::payment_relation::POOL_V1_PAYMENT_STATEMENT_BYTES']
cmd[i:i]=[a for n in consts for a in ['--include',n]]
x.update(attempt='charon-005',command=cmd,change='Include transitive proof/afterstate width constant initializers; unchanged shipped functions',deps_fingerprint={'scope':'same production sources, expanded constant initializer allowlist'})
(B/'charon-005.json').write_text(json.dumps(x,indent=2)+'\n')
x=json.loads((B/'aeneas-003.json').read_text());x.update(attempt='aeneas-004',change='Expose transitive proof/afterstate widths in LLBC; unchanged shipped functions');x['command'][x['command'].index('-dest')+1]=str(B/'generated-v4')
(B/'aeneas-004.json').write_text(json.dumps(x,indent=2)+'\n')
