"""Pin comparison inputs, export only this job's proof objects, inventory own outputs."""
from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path('/home/dombarker/project-offloads/codex-cx-history-persist-20261105')
C=Path('/home/dombarker/project-offloads/codex-cx-history-persist-cache-20261104')
comparison=json.loads((B/'NGR_PIN_COMPARISON.json').read_text())
inputs=[]
for r in comparison['comparisons']['NGK']['mismatches']:
 for kind in ['old','new']:
  p=Path(r[kind+'_path']);sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==r[kind],str(p)
  inputs.append(dict(path=str(p),sha256=sha,bytes=p.stat().st_size))
(B/'NGR_PIN_INPUT_HASHES.json').write_text(json.dumps(inputs,indent=1)+'\n')
out=C/'NGR_exports_20261105';out.mkdir(exist_ok=True);exports=[]
for name in ['NGR_Data','NGR_WriterOutput','NGR_NativeCopy','NGR_HistoryPersist','NGR_COMBINED_IMPORT']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NGR_objects'/(name+suffix)
  if p.is_file():
   q=out/p.name;shutil.copy2(p,q);a=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==a
   exports.append(dict(module=name,path=str(q),sha256=a,bytes=q.stat().st_size,source_sha256=hashlib.sha256((B/'NGR_generated'/(name+'.lean')).read_bytes()).hexdigest()))
(B/'NGR_EXPORT.json').write_text(json.dumps(exports,indent=1)+'\n')
processes=subprocess.check_output(['ps','-u','dombarker','-o','pid=,args='],text=True)
active=[line for line in processes.splitlines() if str(B) in line and any(x in line for x in ['/bin/lean ','/bin/leanc ','NGR_native/NGR_'])]
assert not active,active
inventory=[]
for name in ['NGR_objects','NGR_native','NGR_tmp']:
 p=B/name;files=[x for x in p.rglob('*') if x.is_file()]
 inventory.append(dict(directory=str(p),files=len(files),bytes=sum(x.stat().st_size for x in files)))
summary=dict(cache_retained=True,export_files=len(exports),export_bytes=sum(x['bytes'] for x in exports),own_rebuildable_outputs=inventory,active_owned_provers=active,disk=subprocess.check_output(['df','-h','/'],text=True))
(B/'NGR_HOST_END.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
