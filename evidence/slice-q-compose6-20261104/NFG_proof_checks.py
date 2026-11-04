"""Accepted new objects only; reject drafts, stale parents, or extra axioms."""
from pathlib import Path
import json,hashlib,re
from NFG_dependency_check import check_imports
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def accepted(module):
 rows=[json.loads(p.read_text()) for p in sorted(E.glob('NFG_L*/receipt.json'))]
 selected=[r for r in rows if r.get('module')==module];assert selected,('missing Lean receipt',module)
 r=selected[-1];assert r['exit_status']==0,('failed latest Lean target',module)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(r['swaps'])==0
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit_status']==0 and ad['reservation']['allowed'] is True
 generated=json.loads((E/'NFG_GENERATED.json').read_text());rel=module.replace('.','/')+'.lean';source=E/(generated[module]['path'] if module in generated else rel)
 assert sha(source)==r['source_hashes'][rel],('source drift',module)
 check_imports(source,E,generated,rows)
 lines=r['print_axioms'];assert lines,('missing top axioms audit',module)
 for line in lines:
  if 'depends on axioms:' in line:
   m=re.search(r'\[([^]]*)\]',line);assert m
   assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},('extra axiom',module,line)
 artifact=json.loads((E/a/'object.json').read_text());assert artifact['attempt']==a and artifact['module']==module and artifact['source_sha256']==sha(source)
 return dict(module=module,attempt=a,source_sha256=sha(source),object_sha256=artifact['sha256'],receipt_sha256=sha(E/a/'receipt.json'),axioms=lines,dependencies_sha256=hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest())
