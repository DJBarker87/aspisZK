from pathlib import Path
import json,subprocess,re,hashlib
B=Path(__file__).resolve().parent;rev='e45a05e2626fd85f9e14ca4faf2dee378470c765'
seeds=json.load(open(B/'source-seeds.json'));missing=set(json.load(open(B/'source-seed-missing.json')))
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev],text=True).splitlines();pathset=set(paths)
# Successful compiler receipts bind the separately retained RPz8 source snapshots.
for p in paths:
 if re.fullmatch(r'evidence/replay-dry9-20261027/RPz8_\d+/receipt.json',p):
  d=json.loads(subprocess.check_output(['git','show',rev+':'+p]));m=d.get('module')
  if m in missing and d.get('exit_status')==0:
   source='evidence/replay-dry9-20261027/'+m+'.lean'
   if source not in pathset:continue
   s=subprocess.check_output(['git','show',rev+':'+source]);sha=hashlib.sha256(s).hexdigest()
   if sha in d.get('source_hashes',{}).values():
    seeds[m]=dict(source=source,sha256=sha,revision=rev,basis=p,compiler_source=d.get('sources'));missing.remove(m)
(B/'source-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n');(B/'source-seed-missing.json').write_text(json.dumps(sorted(missing),indent=2)+'\n')
print('remaining project',sorted(m for m in missing if m.split('.')[0] not in ['Aeneas','AeneasMeta','Batteries','Init','Lean','Std','Mathlib','Qq','Aesop']))
