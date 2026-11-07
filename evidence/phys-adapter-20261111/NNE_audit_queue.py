from NNE_formal import *
mode=sys.argv[1]
if mode=='driver':
 r=run('NNE_L052','lean','NNE_ProofDriver')
elif mode=='link':
 admission('NNE_link_sources')
 r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=b.parent/'codex-cx-ledger8-cache-20261104/NGJ_native_seed'/n
 dst=b/'NNE_native'/n;shutil.copy2(src,dst)
 rows.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
 (E/'NNE_AUDIT_C_PINS.json').write_text(r.stdout)
 r=run('NNE_L053','link','NNE_ProofDriver',[json.loads((E/'NNE_ENV.json').read_text())['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNE_native/NNE_ProofDriver','NNE_native/NNE_ProofDriver.c','NNE_native/NFA_WALKER.c','NNE_native/NFA_MemoryLimit.c'])
elif mode=='proofs':
 files={n:(E/n).read_text() for n in ['NNE_batch.py','NNE_AUDIT_ROOTS.json','NNE_AUDIT_MODULES.json']}
 r=run('NNE_L054','audit','proof0',['python3','NNE_batch.py','proof0'],files)
else:raise ValueError(mode)
if isinstance(r,dict):sys.exit(r['exit_status'])
