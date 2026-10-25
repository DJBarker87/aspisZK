#!/usr/bin/env python3
"""Final small handoff manifest; includes statements as evidence dependencies."""
from pathlib import Path
import hashlib,json,platform,resource,subprocess,sys,time
r=Path(__file__).resolve().parents[2];d=r/'evidence/port24sbfmap-20261024';t=time.monotonic()
x=json.loads((d/'selected-implementation.json').read_text());v=json.loads((d/'validation.json').read_text())
assert v['exit_status']==0 and len(v['checks'])==121
assert x['inspection_receipt']['exit_status']==0
for b in x['builds'].values():
 assert b['elf']['text_equal']
changed=subprocess.check_output(['git','diff','--name-only','438cd6f576b97bcf724ef523185a096205b7a18c'],cwd=r,text=True).splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
assert all(p.startswith(('evidence/port24sbfmap-20261024/','tools/port24sbfmap-20261024/')) for p in changed+new)
report=(d/'REPORT.md').read_text();primitives=(d/'PRIMITIVES.md').read_text()
assert 'not yet established' in report and 'No theorem statement/premise changed' in report
assert 'Missing identity is separate from semantics' in primitives
assert 'ptr field then cap field' in primitives and 'No new trust decision is logically forced' in primitives
files=sorted(p for base in [d,r/'tools/port24sbfmap-20261024'] for p in base.iterdir() if p.is_file() and p.name!='manifest.json')
pins={str(p.relative_to(r)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in files}
assert all(p['bytes']<=5_000_000 for k,p in pins.items() if k.endswith('.json'))
u=resource.getrusage(resource.RUSAGE_SELF)
o={'schema':'Port24SBFMAP-source-binding-handoff-v1','claim':'Current retained allocator/caller implementation association only; whole-helper/native primitive semantics and exact sysroot source identity remain open.','command':['python3','tools/port24sbfmap-20261024/Port24SBFMAP_handoff.py'],'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'frozen_source_revision':x['source_revision'],'python':sys.version,'platform':platform.platform(),'exit_status':0,'wall_seconds':time.monotonic()-t,'peak_rss_bytes_macos':u.ru_maxrss,'swaps':u.ru_nswap,'print_axioms':'N/A: zero Lean attempts; no new theorem/axiom','budget_used':{'Lean':0,'Kani':0,'extraction':0,'standalone_Rust':0,'backend':0,'ELF_rebuild':0,'full_manifest':0},'resource_admission':'N/A: small read-only inspection and owned evidence writes only; no build launched','existing_Lean_carry_unspent':7,'global_Lean_charged_lower_bound':332,'global_Lean_total':368,'other_pending_jobs':'Separate, unchanged; not assessed or consumed','dependencies':pins}
(d/'manifest.json').write_text(json.dumps(o,indent=2)+'\n')
print(json.dumps({'exit_status':0,'pinned_files':len(files),'wall_seconds':o['wall_seconds'],'peak_rss_bytes':u.ru_maxrss,'swaps':u.ru_nswap}))
