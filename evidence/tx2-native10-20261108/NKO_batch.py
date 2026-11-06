"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys
B=Path.cwd();mode=sys.argv[1];E=B/'NKO_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode=='all':jobs=[('proof'+str(i),['NKO_native/NKO_ProofDriver','proof'+str(i)]) for i in range(len(json.loads((B/'NKO_AUDIT_ROOTS.json').read_text())['groups']))]
elif mode.startswith('inventory-'):jobs=[(mode,['NKO_native/NKO_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NKO_native/'+('NKO_PoolDriver' if mode=='poolscan' else 'NKO_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan']:jobs=[(mode,['NKO_native/'+('NKO_Driver' if mode=='scan' else 'NKO_ProofDriver'),mode])]
else:
 batch=int(mode.removeprefix('batch'));groups=json.loads((B/'NKO_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NKO_native/NKO_ProofDriver','proof'+str(i)]) for i in range(batch,min(batch+1,len(groups)))];assert jobs
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(dict(target=name,exit_status=r.returncode,wall_seconds=receipt["wall_seconds"],peak_rss_kib=receipt["peak_rss_kib"],swaps=receipt["swaps"],raw_roots=len(receipt["results"]))),flush=True)
 if r.returncode:sys.exit(r.returncode)
