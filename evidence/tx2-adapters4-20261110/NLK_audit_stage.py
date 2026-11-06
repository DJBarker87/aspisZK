from NLK_formal import *
subprocess.run([sys.executable,str(E/'NLK_audit_prepare.py')],check=True)
rc=run('NLK_L054','lean','NLK_COMBINED_IMPORT');assert rc['exit_status']==0
roots=(E/'NLK_AUDIT_ROOTS.json').read_text();groups=json.loads(roots)['groups']
extra={'NLG_AUDIT_ROOTS.json':roots,'NLG_AUDIT_MODULES.json':json.dumps([['NLK_COMBINED_IMPORT'] for _ in groups]),'NLK_audit_one.py':(E/'NLK_audit_one.py').read_text()}
binary='/home/dombarker/project-offloads/codex-cx-ledger21-20261110/NLG_native/NLG_ProofDriver';h='d12d3e28ca5819cc41010e74078c49d7d64eec727472e4401949f6694c9e0675'
rc=run('NLK_L055','audit','fixtures',['python3','NLK_audit_one.py',binary,'fixtures',h],extra=extra);assert rc['exit_status']==0
for i,g in enumerate(groups):
 a=f'NLK_L{56+i:03}';mode='proof'+str(i)
 rc=run(a,'audit',mode,['python3','NLK_audit_one.py',binary,mode,h],extra=extra)
 # The known raw/collector disagreement is retained verbatim, not suppressed.
 if rc['exit_status']!=0:
  assert 'NHC_DecodeModel.decoder_error' in g and rc['exit_status']==1,(a,rc['exit_status'])
after=56+len(groups)
rc=run(f'NLK_L{after:03}','lean','NLK_ScanDriver',extra={'NLK_native/.keep':''});assert rc['exit_status']==0
linkscript='''from pathlib import Path
import json,hashlib,subprocess
b=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_native');pins=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 p=src/n;q=b/'NLK_native'/n;raw=p.read_bytes();q.write_bytes(raw);pins.append(dict(source=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(b/'NLK_AUDIT_LINK_INPUTS.json').write_text(json.dumps(pins,indent=1)+'\\n')
r=subprocess.run(['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','leanc','-O3','-rdynamic','-o','NLK_native/NLK_ScanDriver','NLK_native/NFA_WALKER.c','NLK_native/NLK_ScanDriver.c','NLK_native/NFA_MemoryLimit.c'])
assert r.returncode==0,r.returncode
p=b/'NLK_native/NLK_ScanDriver';(b/'NLK_SCAN_BINARY.json').write_text(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)))
'''
rc=run(f'NLK_L{after+1:03}','link','NLK_ScanDriver',['python3','NLK_link.py'],extra={'NLK_link.py':linkscript});assert rc['exit_status']==0
r=ssh('python3',f"from pathlib import Path;print(Path({B!r},'NLK_SCAN_BINARY.json').read_text())");assert r.returncode==0
scan=json.loads(r.stdout);(E/'NLK_SCAN_BINARY.json').write_text(r.stdout)
rc=run(f'NLK_L{after+2:03}','audit','scan',['python3','NLK_audit_one.py','NLK_native/NLK_ScanDriver','scan',scan['sha256']],extra={'NLK_EXPECTED_IMPORTS.jsonl':(E/'NLK_EXPECTED_IMPORTS.jsonl').read_text(),'NLK_audit_one.py':(E/'NLK_audit_one.py').read_text()});assert rc['exit_status']==0
# JSON transport cannot carry arbitrary compressed bytes: one pinned text version is
# uploaded for validation, then removed only after the scope has completed.
pins=lzma.decompress((E/'NLK_PREDECESSOR_PINS.json.xz').read_bytes()).decode()
pin=(E/'NLK_pin.py').read_text().replace("json.loads(lzma.decompress((B/'NLK_PREDECESSOR_PINS.json.xz').read_bytes()))","json.loads((B/'NLK_PREDECESSOR_PINS.json').read_text())")
rc=run(f'NLK_L{after+3:03}','cache','NLK_CohortPins',['python3','NLK_pin.py'],extra={'NLK_pin.py':pin,'NLK_PREDECESSOR_PINS.json':pins});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json,lzma,hashlib
b=Path({B!r});names=['NLK_CLOSURE_PINS.json','NLK_LOADED_scan.jsonl','NLK_AUDIT_LINK_INPUTS.json']+list(p.name for p in b.glob('NLK_binary_*.json'))
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/n
 if n.endswith('.jsonl') or n=='NLK_CLOSURE_PINS.json':p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 else:p.write_text(t)
print('COMBINED_AUDIT_COMPLETE',flush=True)
