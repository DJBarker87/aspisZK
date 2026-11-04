"""Own-source and own-object freshness, recursively; no host changes."""
from pathlib import Path
import hashlib,json,re

def check_imports(source_file,E,generated,receipts=None):
 records=receipts if receipts is not None else [json.loads(p.read_text()) for p in sorted(E.glob('NFG_L*/receipt.json'))]
 seen={}
 def visit(source,parent=None):
  for line in source.read_text().splitlines():
   if not line.startswith('import '):continue
   for dep in line[7:].split():
    if not dep.startswith('NFG_'):continue
    own=[r for r in records if r.get('module')==dep]
    assert own,('own dependency has no receipt',dep)
    last=own[-1]
    assert last['exit_status']==0,('stale own object after failed compile',dep,last['attempt'])
    for line in last['print_axioms']:
     if 'depends on axioms:' in line:
      found=re.search(r'\[([^]]*)\]',line);assert found is not None
      assert {x.strip() for x in found.group(1).split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},('nonstandard own dependency axiom',dep,line)
    dr=dep.replace('.','/')+'.lean';sf=E/(generated[dep]['path'] if dep in generated else dr)
    assert hashlib.sha256(sf.read_bytes()).hexdigest()==last['source_hashes'][dr],('own dependency source drift',dep)
    artifact=json.loads((E/last['attempt']/'object.json').read_text())
    assert artifact['attempt']==last['attempt'] and artifact['module']==dep
    assert artifact['source_sha256']==last['source_hashes'][dr]
    if parent is not None:
     pins=parent['deps_fingerprint']['selected_objects']
     found=[v for k,v in pins.items() if k.endswith('/'+dep.replace('.','/')+'.olean')]
     assert len(found)==1 and found[0]['sha256']==artifact['sha256'],('parent imported older own object',parent['attempt'],dep)
    if dep in seen:continue
    seen[dep]=artifact
    visit(sf,last)
 visit(source_file)
 return seen
