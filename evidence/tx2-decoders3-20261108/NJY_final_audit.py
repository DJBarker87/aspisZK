from NJY_formal import *
import base64
assert json.loads((E/'NJY_L018/receipt.json').read_text())['exit_status']==0
for n in ['NJY_AUDIT.json','NJY_EXPORT.json','NJY_PREDECESSOR_COMPARISON.json','NJY_CLOSURE_PINS.json.xz','NJY_CLOSURE_PINS.json.sha256','NJY_NJY_LOADED_scan.jsonl.xz','NJY_NJY_LOADED_scan.jsonl.sha256']:
 p=E/n;q=E/n.replace('NJY_','NJY_INITIAL_',1)
 if p.exists()and not q.exists():q.write_bytes(p.read_bytes())
assert run('NJY_L020','lean','NJY_COMBINED_IMPORT')['exit_status']==0
pins=json.loads((E/'NJY_AUDIT_BINARIES.json').read_text());proof=pins['proof_path'];proofhash=pins['proof_sha256']
for a,mode,binary,h in [('NJY_L021','fixtures',proof,proofhash),('NJY_L022','proof0',proof,proofhash),('NJY_L023','scan','NJY_native/NJY_ScanDriver',pins['scan_sha256'])]:
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
assert run('NJY_L024','pin','NJY_pin',['python3','NJY_pin.py'],{'NJY_pin.py':(E/'NJY_pin.py').read_text()})['exit_status']==0
r=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in ['NJY_CLOSURE_PINS.json.xz','NJY_CLOSURE_PINS.json.sha256','NJY_PREDECESSOR_COMPARISON.json','NJY_EXPORT.json']}}))")
assert r.returncode==0
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
