from NMM_formal import *
MODE=sys.argv[1];A=sys.argv[2]
BINARY='/home/dombarker/project-offloads/codex-cx-ledger21-20261110/NLG_native/NLG_ProofDriver'
PIN='d12d3e28ca5819cc41010e74078c49d7d64eec727472e4401949f6694c9e0675'
if MODE=='combined':
 subprocess.run([sys.executable,str(E/'NMM_audit_prepare.py')],check=True)
 r=run(A,'lean','NMM_COMBINED_IMPORT')
elif MODE in ['fixtures','proof0']:
 roots=(E/'NMM_AUDIT_ROOTS.json').read_text();groups=json.loads(roots)['groups']
 extra={'NLG_AUDIT_ROOTS.json':roots,'NLG_AUDIT_MODULES.json':json.dumps([['NMM_COMBINED_IMPORT'] for _ in groups]),'NMM_audit_one.py':(E/'NMM_audit_one.py').read_text()}
 r=run(A,'audit',MODE,['python3','NMM_audit_one.py',BINARY,MODE,PIN],extra=extra)
elif MODE=='scan_compile':
 r=run(A,'lean','NMM_ScanDriver',extra={'NMM_native/.keep':''})
elif MODE=='link':
 code='''from pathlib import Path
import json,hashlib,subprocess
b=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_native');pins=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=src/n;q=b/'NMM_native'/n;raw=p.read_bytes();q.write_bytes(raw);pins.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(b/'NMM_AUDIT_LINK_INPUTS.json').write_text(json.dumps(pins,indent=1)+'\\n')
r=subprocess.run(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NMM_native/NMM_ScanDriver','NMM_native/NFA_WALKER.c','NMM_native/NMM_ScanDriver.c','NMM_native/NFA_MemoryLimit.c'])
assert r.returncode==0,r.returncode
p=b/'NMM_native/NMM_ScanDriver';(b/'NMM_SCAN_BINARY.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
'''
 r=run(A,'link','NMM_ScanDriver',['python3','NMM_link.py'],extra={'NMM_link.py':code})
elif MODE=='scan':
 x=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NMM_SCAN_BINARY.json').read_text())");assert x.returncode==0
 scan=json.loads(x.stdout);(E/'NMM_SCAN_BINARY.json').write_text(x.stdout)
 r=run(A,'audit','scan',['python3','NMM_audit_one.py','NMM_native/NMM_ScanDriver','scan',scan['sha256']],extra={'NMM_EXPECTED_IMPORTS.jsonl':(E/'NMM_EXPECTED_IMPORTS.jsonl').read_text(),'NMM_audit_one.py':(E/'NMM_audit_one.py').read_text()})
else:raise ValueError(MODE)
sys.exit(r['exit_status'])
