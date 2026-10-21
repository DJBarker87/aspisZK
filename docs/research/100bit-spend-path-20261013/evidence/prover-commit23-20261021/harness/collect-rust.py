"""Retain exact tool receipts; explicit acceptance is narrower than exit zero."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit23-20261021';host='dombarker@100.108.41.90'
f=E/'rust-attempts.json';rows={x['name']:x for x in json.loads(f.read_text())} if f.exists() else {}
for name in sys.argv[1:]:
 d=E/'receipts'/name;d.mkdir(exist_ok=True,parents=True)
 for n in ['receipt.json','stdout.log','stderr.log','time.log']:
  subprocess.run(['scp',host+':'+H+'/receipts/'+name+'/'+n,str(d/n)],check=True)
 subprocess.run(['scp',host+':'+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
 x=json.loads((d/'receipt.json').read_text());pins=json.loads((E/(name+'-inputs.json')).read_text())
 assert x['swaps']==0
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 stdout=(d/'stdout.log').read_text()
 x.update(name=name,accepted=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in stdout,
          source_revision=pins['source_revision'],production_source_revision='cb9372b8f',
          source_identity='Exact full instrumented source hashes in input manifest; production-prefix binding checked separately.',
          input_manifest=name+'-inputs.json',print_axioms='N/A: Rust/Kani/Charon; promoted Lean checked separately')
 if name.startswith(('sim-tail-control-v2-',)):
  x['accepted']=x['exit_status']==0
 if name=='tail-runtime-v1':
  x['accepted']=x['exit_status']==0 and 'test result: ok. 2 passed' in stdout
 x['acceptance_scope']='single target only; fixture runtime checks are not universal refinement; no whole simulator or OS law'
 rows[name]=x
f.write_text(json.dumps(list(rows.values()),indent=2)+'\n')
print([(x['name'],x['exit_status'],x['accepted']) for x in rows.values()])
