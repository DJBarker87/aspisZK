from NMX_formal import *
mode=sys.argv[1]
if mode=='driver':
 r=run('NMX_L044','lean','NMX_ProofDriver')
elif mode=='link':
 admission('NMX_link_sources')
 r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});rows=[]
for n in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 src=b.parent/'codex-cx-ledger8-cache-20261104/NGJ_native_seed'/n
 dst=b/'NMX_native'/n;shutil.copy2(src,dst)
 rows.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest()))
print(json.dumps(rows))
''');assert r.returncode==0,r.stderr
 (E/'NMX_AUDIT_C_PINS.json').write_text(r.stdout)
 r=run('NMX_L045','link','NMX_ProofDriver',[json.loads((E/'NMX_ENV.json').read_text())['LEAN_SYSROOT']+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NMX_native/NMX_ProofDriver','NMX_native/NMX_ProofDriver.c','NMX_native/NFA_WALKER.c','NMX_native/NFA_MemoryLimit.c'])
elif mode=='proofs':
 groups=json.loads((E/'NMX_AUDIT_ROOTS.json').read_text())['groups']
 for i in range(len(groups)):
  files={n:(E/n).read_text() for n in ['NMX_batch.py','NMX_AUDIT_ROOTS.json','NMX_AUDIT_MODULES.json']}
  r=run('NMX_L'+str(46+i).zfill(3),'audit','proof'+str(i),['python3','NMX_batch.py','proof'+str(i)],files)
  if r['exit_status']:break
else:raise ValueError(mode)
if isinstance(r,dict):sys.exit(r['exit_status'])
