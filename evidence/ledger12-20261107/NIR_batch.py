"""Each native child runs sequentially and has independent time/RSS/axiom receipt."""
from pathlib import Path
import subprocess,json,time,hashlib,re,sys
B=Path.cwd();mode=sys.argv[1];E=B/'NIR_audit'/mode;E.mkdir(parents=True,exist_ok=True)
if mode.startswith('inventory-'):jobs=[(mode,['NIR_native/NIR_InventoryDriver',mode.split('-')[1]])]
elif mode in ['poolfixtures','poolroots','poolscan']:jobs=[('scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0',['NIR_native/'+('NIR_PoolDriver' if mode=='poolscan' else 'NIR_PoolProofDriver'), 'scan' if mode=='poolscan' else 'fixtures' if mode=='poolfixtures' else 'proof0'])]
elif mode in ['fixtures','scan','scan2']:jobs=[('scan' if mode=='scan2' else mode,['NIR_native/'+('NIR_Driver' if mode.startswith('scan') else 'NIR_ProofDriver'),'scan' if mode=='scan2' else mode])]
else:
 batch=int(mode.removeprefix('batch'));groups=json.loads((B/'NIR_AUDIT_ROOTS.json').read_text())['groups'];jobs=[('proof'+str(i),['NIR_native/NIR_ProofDriver','proof'+str(i)]) for i in range(batch,min(batch+1,len(groups)))];assert jobs
for name,command in jobs:
 start=time.monotonic()
 with (E/(name+'.log')).open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1] if m else None
 receipt=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],results=[json.loads(l[11:]) for l in raw.splitlines() if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n');print(json.dumps(receipt),flush=True)
 if r.returncode:print(raw,flush=True);sys.exit(r.returncode)
if mode=='batch27':
 import os,lzma,shutil
 roots=os.environ['LEAN_PATH'].split(':');loaded=[json.loads(l)for l in (B/'NIR_LOADED_scan.jsonl').read_text().splitlines()];pins=[]
 for row in loaded:
  rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p,rel
  for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
   if q.is_file():pins.append(dict(module=row['module'],path=str(q),suffix=str(q)[len(str(p)):],sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 manifest=dict(LEAN_PATH=roots,selected_objects=pins,modules=len(loaded),full_composition_pass=True)
 raw=(json.dumps(manifest,indent=1)+'\n').encode();(B/'NIR_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NIR_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 cache=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIR_20261107/NIR_exports_20261107');cache.mkdir(exist_ok=True);exports=[]
 for p in (B/'NIR_objects').rglob('*'):
  if p.is_file():
   q=cache/p.relative_to(B/'NIR_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);exports.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 (B/'NIR_EXPORT.json').write_text(json.dumps(dict(export=str(cache),files=exports,bytes=sum(r['bytes']for r in exports),cache_retained=True,disk_free=shutil.disk_usage(B).free),indent=1)+'\n')
 print('NIR closure pinned and own objects exported',flush=True)
