"""Optimized link and raw/fixture/scan gate, each child independently timed."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys
B=Path.cwd();E=B/'NFS_final_audit';E.mkdir(exist_ok=True)
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
config=json.loads((B/sys.argv[1]).read_text())
roots=json.loads((B/'NFS_AUDIT_ROOTS.json').read_text())
common=['NFS_native/NFA_WALKER.c','NFS_native/NFA_MemoryLimit.c']
jobs=[('linkproof',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NFS_native/NFS_ProofDriver','NFS_native/NFS_ProofDriver.c',*common]),('linkscan',[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NFS_native/NFS_Driver','NFS_native/NFS_Driver.c',*common]),('fixtures',['NFS_native/NFS_ProofDriver','fixtures'])]
jobs += [(f'proof{i}',['NFS_native/NFS_ProofDriver',f'proof{i}']) for i in range(len(roots['groups']))]
jobs += [('scan',['NFS_native/NFS_Driver','scan'])]
all_receipts=[]
for name,command in jobs:
 log=E/(name+'.log');timing=E/(name+'.time');started=time.monotonic()
 with log.open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=log.read_text();s=timing.read_text()
 def metric(key):
  m=re.search(re.escape(key)+r':\s*(.*)',s);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-started,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),source_revision=config['source_revision'],source_sha256={p:hashlib.sha256((B/p).read_bytes()).hexdigest() for p in config['sources']},print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l] if name.startswith('proof') or name=='fixtures' else 'N/A: optimized linker or incoherence scan')
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');all_receipts.append(receipt)
 print(name,json.dumps({k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 print(raw,flush=True)
 if r.returncode:sys.exit(r.returncode)
(E/'NFS_CHILD_ATTEMPTS.json').write_text(json.dumps(all_receipts,indent=1)+'\n')
