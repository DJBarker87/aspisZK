#!/usr/bin/env python3
"""Preserve every success/failure receipt; exit zero alone is not acceptance."""
from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit18-20261021'
host='dombarker@100.108.41.90'
rows=[]
for name in sys.argv[1:]:
 d=E/'receipts'/name;d.mkdir(exist_ok=True,parents=True)
 for f in ['receipt.json','stdout.log','stderr.log','time.log']:
  subprocess.run(['scp',host+':'+H+'/receipts/'+name+'/'+f,str(d/f)],check=True)
 subprocess.run(['scp',host+':'+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
 x=json.loads((d/'receipt.json').read_text());pins=json.loads((E/(name+'-inputs.json')).read_text())
 assert x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 stdout=(d/'stdout.log').read_text();stderr=(d/'stderr.log').read_text()
 x.update(name=name,accepted=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in stdout,
          source_revision=pins['source_revision'],production_source_revision='c35b7b481402f81e2ea5c967c4c61d5b8dc01d5d',
          source_revision_note='Host revision marker inherited from part 17; exact task source hashes and current production-prefix binding are in source-binding.json.',
          input_manifest=name+'-inputs.json',print_axioms='N/A: Rust/Kani/Charon, not Lean')
 if name.startswith('simcoin-') and 'transition' not in name:
  x.update(accepted=x['exit_status']==0,print_axioms='N/A: extraction; corresponding promoted Lean targets audited separately')
 if name=='sim-charon-v1':
  x.update(accepted=False,exclusion='LLBC has_errors=true; extractor script refused Aeneas promotion despite cargo exit zero')
 rows.append(x)
(E/'rust-attempts.json').write_text(json.dumps(rows,indent=2)+'\n')
print([(x['name'],x['exit_status'],x['accepted'],x['wall_seconds']) for x in rows])
