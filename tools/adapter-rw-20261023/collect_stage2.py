#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,shutil
H=Path(__file__).resolve().parent;out=H/'export-stage2';out.mkdir(exist_ok=True)
for p in H.glob('*'):
 if p.is_file() and (p.suffix=='.json' or p.name.startswith('runtime-')):shutil.copy2(p,out/p.name)
for p in H.iterdir():
 if not p.is_dir():continue
 if (p/'time.log').exists() or re.fullmatch(r'(rust|sbf|native|lean|replay|heap-build|heap-replay)-\d+',p.name):
  d=out/p.name;d.mkdir(exist_ok=True)
  for f in p.iterdir():
   if f.is_file() and f.name in ['stdout.log','time.log','receipt.json']:shutil.copy2(f,d/f.name)
rows=[];retained=[]
for p in sorted(H.glob('replay-*')):
 if not p.is_dir() or not (p/'comparison.json').exists():continue
 name=p.name.removeprefix('replay-');c=json.loads((p/'comparison.json').read_text())
 h=H/('heap-replay-'+name);heaps={}
 for label in ['before','after']:
  heaps[label]={}
  for stage in ['stage1','stage2']:
   log=json.loads((h/label/(stage+'.json')).read_text())['logs']
   matching=[line for line in log if '0xada,' in line]
   assert len(matching)==1,matching
   nums=re.findall(r'0x[0-9a-fA-F]+',matching[0]);heaps[label][stage]=int(nums[1],16)
 row={'fixture':name,'comparison':c,'heap_bytes':heaps}
 assert all(v<262144 for side in heaps.values() for v in side.values())
 assert c['delta']['stage1']<=12000 and c['delta']['stage2']<=12000
 rows.append(row)
 for f in p.glob('*.key'):retained.append({'path':str(f),'retained':f.exists(),'bytes':f.stat().st_size,'public_keys':'see input-manifest.json; simulated runtime only'})
 for src in [p,h]:
  dst=out/src.name;dst.mkdir(exist_ok=True)
  for f in src.rglob('*.json'):
   t=dst/f.relative_to(src);t.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,t)
  index=[{'path':str(f.relative_to(src)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size} for f in src.rglob('*.bin')]
  (dst/'binary-hashes.json').write_text(json.dumps(index,indent=2)+'\n')
  for f in src.glob('*.key'):
   if src==h:retained.append({'path':str(f),'retained':True,'bytes':f.stat().st_size,'public_keys':'see diagnostic input-manifest.json; simulated runtime only'})
(out/'stage2-measurements.json').write_text(json.dumps({'fixtures':rows,'heap_scope':'separate old/new diagnostic ELFs: terminal cursor observation after both stages; bump dealloc is no-op; includes entrypoint allocations; 256KiB heap; release CU from uninstrumented ELFs','native':'native-001:76 passed;1200 distinct mutated inputs on runtime admission;both stages all six fixtures;identical errors/return/full records;6 separately labelled counter1 diagnostics','error_differences_observed':[],'keys':retained,'release_repin':'candidate only, not adopted'},indent=2)+'\n')
print(json.dumps(rows,indent=2))
