from NLA_formal import *
import difflib
subprocess.run([sys.executable,str(E/'NLA_audit_prepare.py')],check=True)
rc=run('NLA_L020','lean','NLA_COMBINED_IMPORT');assert rc['exit_status']==0
# Reuse the identical hardened proof binary, with mutable input ROOT LISTS only.
roots=(E/'NLA_AUDIT_ROOTS.json').read_text()
extra={'NIS_AUDIT_ROOTS.json':roots,'NIM_AUDIT_MODULES.json':json.dumps([['NLA_COMBINED_IMPORT']]),'NLA_EXPECTED_IMPORTS.jsonl':(E/'NLA_EXPECTED_IMPORTS.jsonl').read_text(),'NLA_audit_one.py':(E/'NLA_audit_one.py').read_text()}
binary='/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NJQ_native/NJQ_RetainedProofDriver';h='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
for a,mode in [('NLA_L021','fixtures'),('NLA_L022','proof0')]:
 rc=run(a,'audit',mode,['python3','NLA_audit_one.py',binary,mode,h],extra=extra);assert rc['exit_status']==0
rc=run('NLA_L023','lean','NLA_ScanDriver',extra={'NLA_native/.keep':''});assert rc['exit_status']==0
# Pin/copy only the unchanged generated C of the existing walker and memory cap.
linkscript='''from pathlib import Path
import shutil,json,hashlib,subprocess
b=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_native');pins=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=src/n;q=b/'NLA_native'/n;raw=p.read_bytes();q.write_bytes(raw);pins.append(dict(source=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(b/'NLA_AUDIT_LINK_INPUTS.json').write_text(json.dumps(pins,indent=1)+'\\n')
r=subprocess.run(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NLA_native/NLA_ScanDriver','NLA_native/NFA_WALKER.c','NLA_native/NLA_ScanDriver.c','NLA_native/NFA_MemoryLimit.c'])
assert r.returncode==0,r.returncode
p=b/'NLA_native/NLA_ScanDriver';(b/'NLA_SCAN_BINARY.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
'''
rc=run('NLA_L024','link','NLA_ScanDriver',['python3','NLA_link.py'],extra={'NLA_link.py':linkscript});assert rc['exit_status']==0
r=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NLA_SCAN_BINARY.json').read_text())");assert r.returncode==0
scan=json.loads(r.stdout);(E/'NLA_SCAN_BINARY.json').write_text(r.stdout)
rc=run('NLA_L025','audit','scan',['python3','NLA_audit_one.py','NLA_native/NLA_ScanDriver','scan',scan['sha256']],extra={'NLA_EXPECTED_IMPORTS.jsonl':(E/'NLA_EXPECTED_IMPORTS.jsonl').read_text(),'NLA_audit_one.py':(E/'NLA_audit_one.py').read_text()});assert rc['exit_status']==0
rc=run('NLA_L026','cache','NLA_CohortPins',['python3','NLA_pin.py'],extra={n:(E/n).read_text() for n in ['NLA_pin.py','NLA_PREDECESSOR_PINS.json']});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=['NLA_CLOSURE_PINS.json','NLA_LOADED_scan.jsonl','NLA_AUDIT_LINK_INPUTS.json']+list(p.name for p in b.glob('NLA_binary_*.json'))
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/n
 if n.endswith('.jsonl') or n=='NLA_CLOSURE_PINS.json':p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 else:p.write_text(t)
print('COMBINED_AUDIT_COMPLETE',flush=True)
