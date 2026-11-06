from NKP_formal import *
import difflib
# Four new focused modules must be green before this ONE combined gate.
rc=run('NKP_L006','lean','NKP_RegistryCuts');assert rc['exit_status']==0
subprocess.run([sys.executable,str(E/'NKP_audit_prepare.py')],check=True)
rc=run('NKP_L007','lean','NKP_COMBINED_IMPORT');assert rc['exit_status']==0
# Reuse the identical hardened proof binary, with mutable input ROOT LISTS only.
roots=(E/'NKP_AUDIT_ROOTS.json').read_text()
extra={'NIS_AUDIT_ROOTS.json':roots,'NIM_AUDIT_MODULES.json':json.dumps([['NKP_COMBINED_IMPORT']]),'NKP_EXPECTED_IMPORTS.jsonl':(E/'NKP_EXPECTED_IMPORTS.jsonl').read_text(),'NKP_audit_one.py':(E/'NKP_audit_one.py').read_text()}
binary='/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NJQ_native/NJQ_RetainedProofDriver';h='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
for a,mode in [('NKP_L008','fixtures'),('NKP_L009','proof0')]:
 rc=run(a,'audit',mode,['python3','NKP_audit_one.py',binary,mode,h],extra=extra);assert rc['exit_status']==0
rc=run('NKP_L010','lean','NKP_ScanDriver',extra={'NKP_native/.keep':''});assert rc['exit_status']==0
# Pin/copy only the unchanged generated C of the existing walker and memory cap.
linkscript='''from pathlib import Path
import shutil,json,hashlib,subprocess
b=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters-20261107/NKF_native');pins=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=src/n;q=b/'NKP_native'/n;raw=p.read_bytes();q.write_bytes(raw);pins.append(dict(source=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(b/'NKP_AUDIT_LINK_INPUTS.json').write_text(json.dumps(pins,indent=1)+'\\n')
r=subprocess.run(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NKP_native/NKP_ScanDriver','NKP_native/NFA_WALKER.c','NKP_native/NKP_ScanDriver.c','NKP_native/NFA_MemoryLimit.c'])
assert r.returncode==0,r.returncode
p=b/'NKP_native/NKP_ScanDriver';(b/'NKP_SCAN_BINARY.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
'''
rc=run('NKP_L011','link','NKP_ScanDriver',['python3','NKP_link.py'],extra={'NKP_link.py':linkscript});assert rc['exit_status']==0
r=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NKP_SCAN_BINARY.json').read_text())");assert r.returncode==0
scan=json.loads(r.stdout);(E/'NKP_SCAN_BINARY.json').write_text(r.stdout)
rc=run('NKP_L012','audit','scan',['python3','NKP_audit_one.py','NKP_native/NKP_ScanDriver','scan',scan['sha256']],extra={'NKP_EXPECTED_IMPORTS.jsonl':(E/'NKP_EXPECTED_IMPORTS.jsonl').read_text(),'NKP_audit_one.py':(E/'NKP_audit_one.py').read_text()});assert rc['exit_status']==0
rc=run('NKP_L013','cache','NKP_CohortPins',['python3','NKP_pin.py'],extra={n:(E/n).read_text() for n in ['NKP_pin.py','NKP_PREDECESSOR_PINS.json']});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=['NKP_CLOSURE_PINS.json','NKP_LOADED_scan.jsonl','NKP_AUDIT_LINK_INPUTS.json']+list(p.name for p in b.glob('NKP_binary_*.json'))
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/n
 if n.endswith('.jsonl') or n=='NKP_CLOSURE_PINS.json':p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 else:p.write_text(t)
print('COMBINED_AUDIT_COMPLETE',flush=True)
