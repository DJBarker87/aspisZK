"""One combined gate, unchanged raw ax2 binary; NFX name/list adaptations only."""
from NJY_formal import *
from NJY_inspect import inputs
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
assert run('NJY_L015','lean','NJY_WindowStep')['exit_status']==0
assert run('NJY_L007','lean','NJY_Roots')['exit_status']==0
assert run('NJY_L008','lean','NJY_COMBINED_IMPORT')['exit_status']==0
assert run('NJY_L009','lean','NJY_ScanDriver',extra={'NJY_native/.keep':'owned optimized audit outputs\n'})['exit_status']==0
r=ssh('cat '+B+'/NJY_native/NJY_ScanDriver.c');assert r.returncode==0
files={'NJY_native/NJY_ScanDriver.c':r.stdout}
old=inputs('NJQ_L070')
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:files['NJY_native/'+n]=old['NJQ_native/'+n]
assert run('NJY_L010','link','NJY_ScanDriver',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NJY_native/NJY_ScanDriver',*files],files)['exit_status']==0
proof='/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NJQ_native/NJQ_RetainedProofDriver';proofhash='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
r=ssh('python3',f'''from pathlib import Path
import hashlib,json
p=Path({proof!r});assert hashlib.sha256(p.read_bytes()).hexdigest()=={proofhash!r};q=Path({B!r})/'NJY_native/NJY_ScanDriver';print(json.dumps(dict(proof_path=str(p),proof_sha256={proofhash!r},proof_bytes=p.stat().st_size,scan_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),scan_bytes=q.stat().st_size)))
''');assert r.returncode==0
pins=json.loads(r.stdout);(E/'NJY_AUDIT_BINARIES.json').write_text(json.dumps(pins,indent=1)+'\n')
for a,mode,binary,h in [('NJY_L011','fixtures',proof,proofhash),('NJY_L012','proof0',proof,proofhash),('NJY_L013','scan','NJY_native/NJY_ScanDriver',pins['scan_sha256'])]:
 files={'NIS_AUDIT_ROOTS.json':(E/'NJY_AUDIT_ROOTS.json').read_text(),'NIM_AUDIT_MODULES.json':json.dumps([['NJY_COMBINED_IMPORT']]),'NJY_EXPECTED_IMPORTS.jsonl':(E/'NJY_EXPECTED_IMPORTS.jsonl').read_text(),'NJY_audit_one.py':(E/'NJY_audit_one.py').read_text()}
 rc=run(a,'audit',mode,['python3','NJY_audit_one.py',binary,mode,h],files)
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});paths=list(b.glob('NEP_'+{mode!r}+'_*_REACHABLE.txt'))+[b/('NJY_binary_'+{mode!r}+'.json')]
if {mode!r}=='scan':paths+=[b/'NJY_LOADED_scan.jsonl']
print(json.dumps({{p.name:p.read_text()for p in paths if p.is_file()}}))
''');assert r.returncode==0
 for n,t in json.loads(r.stdout).items():
  p=E/('NJY_'+n)
  if n.endswith('.json'):p.write_text(t)
  else:p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 assert rc['exit_status']==0,(a,rc['exit_status'])
 print(json.dumps(dict(audit_mode=mode,exit=rc['exit_status'])),flush=True)

assert run('NJY_L014','pin','NJY_pin',['python3','NJY_pin.py'],{'NJY_pin.py':(E/'NJY_pin.py').read_text()})['exit_status']==0
r=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in ['NJY_CLOSURE_PINS.json.xz','NJY_CLOSURE_PINS.json.sha256','NJY_PREDECESSOR_COMPARISON.json','NJY_EXPORT.json']}}))")
assert r.returncode==0
import base64
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
