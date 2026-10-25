#!/usr/bin/env python3
"""Read-only pinned-input preflight; never invokes Lean."""
import json, subprocess, sys
from pathlib import Path
from Port31DATA_run import T,E,SYS,pin,state,safe
REV='74a62fd7b6'
def obj(p,rev=REV):return json.loads(subprocess.check_output(['git','show',rev+':'+p]))
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def base(n):
 src=T/('Port31DATA_Bool.lean' if n==353 else 'Port31DATA_Raw.lean')
 old=obj('evidence/port29sdkdata-20261025/Port29SDKDATA_diagnostic-1-preparation.json')
 paths=[Path(r['path']) for r in old['runtime']]+[src,T/'Port31DATA_run.py',Path('/Users/dominic/ZK/AGENTS.md')]
 rules=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad')
 paths += [rules/'r1p-common.txt',rules/'local-lean.txt']
 for name in ['Init.lean','Lean/Environment.lean','Lean/Declaration.lean','Lean/Expr.lean','Lean/Data/KVMap.lean','Init/Data/Bool.lean','Init/Grind/Lemmas.lean']:
  paths.append(SYS/'src/lean'/name)
 paths += [p for p in (SYS/'lib/lean').glob('Init.olean*')]
 fresh=[pin(safe(p)) for p in paths]
 for r in old['runtime']:assert pin(r['path'])==r
 return dict(directory=f'/private/tmp/Port31DATA-{n}-20261025',fresh_pins=fresh,states=[dict(path=str(p),stat=state(safe(p))) for p in paths],sysroot=str(SYS),toolchain='Lean4.32.0; text/core/runtime bytes pinned; no CLI version probe',host_jobs=0,axioms='pending' if n==353 else 'N/A',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
if __name__=='__main__':
 n=int(sys.argv[1]);assert n==353
 r=base(n);write(E/f'Port31DATA_preflight-{n}.json',r)
 print(json.dumps(dict(directory=r['directory'],fresh_pins=len(r['fresh_pins']),lean_calls=0)))
