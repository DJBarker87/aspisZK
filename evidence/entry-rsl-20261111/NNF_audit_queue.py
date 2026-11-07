from NNF_formal import *
mode=sys.argv[1]
if mode=='driver':
 r=run('NNF_L014','lean','NNF_ProofDriver')
elif mode=='link':
 admission('NNF_link_sources')
 r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=b.parent/'codex-cx-ledger8-cache-20261104/NGJ_native_seed'/n
 dst=b/'NNF_native'/n;shutil.copy2(src,dst)
 rows.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
 (E/'NNF_AUDIT_C_PINS.json').write_text(r.stdout)
 r=run('NNF_L015','link','NNF_ProofDriver',[json.loads((E/'NNF_ENV.json').read_text())['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNF_native/NNF_ProofDriver','NNF_native/NNF_ProofDriver.c','NNF_native/NFA_WALKER.c','NNF_native/NFA_MemoryLimit.c'])
elif mode=='proofs':
 groups=json.loads((E/'NNF_AUDIT_ROOTS.json').read_text())['groups']
 for i in range(len(groups)):
  files={n:(E/n).read_text() for n in ['NNF_batch.py','NNF_AUDIT_ROOTS.json','NNF_AUDIT_MODULES.json']}
  r=run('NNF_L'+str(16+i).zfill(3),'audit','proof'+str(i),['python3','NNF_batch.py','proof'+str(i)],files)
  if r['exit_status']:break
else:raise ValueError(mode)
if isinstance(r,dict):sys.exit(r['exit_status'])
