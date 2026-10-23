#!/usr/bin/env python3
"""Generate source-pinned exact type comparisons, at most 100 names per job."""
import argparse,collections,hashlib,json,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/import-union-20261022'
p=argparse.ArgumentParser();p.add_argument('enumeration',type=Path);p.add_argument('plan',type=Path);p.add_argument('staging',type=Path);a=p.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=collections.defaultdict(list);modules={}
for l in a.enumeration.read_text().splitlines():
 k,v=l.split(' ',1);v=json.loads(v)
 if k=='RAW_DECL':names[v[0]].append(v[1:])
 if k=='RAW_MODULE':modules[v[0]]={'path':v[1],'imports':v[2]}
dups=sorted((n,os) for n,os in names.items() if len(os)>1)
template=(ROOT/'tools/import-union/RawDuplicateTypes.lean.in').read_text()
plan=json.loads(a.plan.read_text());plan['ordered']=[r for r in plan['ordered'] if not r['module'].startswith('ImportUnionRawDuplicateBatch')];out=E/'raw-batches';out.mkdir(exist_ok=True)
a.staging.mkdir(exist_ok=True,parents=True);batches=[]
quote=lambda s:json.dumps(s,ensure_ascii=False)
for i,start in enumerate(range(0,len(dups),100)):
 chunk=dups[start:start+100];module=f'ImportUnionRawDuplicateBatch{i:03}'
 requests='#['+',\n'.join('('+quote(n)+', #['+', '.join('('+quote(o)+', '+quote(k)+')' for o,k in os)+'])' for n,os in chunk)+']'
 output=f'evidence/raw-batch-{i:03}.jsonl'
 source=out/(module+'.lean');source.write_text(template.replace('REQUESTS',requests).replace('OUTPUT',output))
 dest=a.staging/'sources'/(module+'.lean');dest.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(source,dest)
 rec={'module':module,'path':str(source.relative_to(ROOT)),'sha256':sha(source),'imports':['Lean'],'affected':False,'rebuild_epoch':'complete-raw-census-type-batches-v1:'+next(r.get('rebuild_epoch','initial') for r in plan['ordered'] if r['module']=='RawUnionScan')}
 plan['ordered'].append(rec);batches.append({'module':module,'output':output,'names':[n for n,_ in chunk],'source':rec})
manifest={'enumeration_sha256':sha(a.enumeration),'modules':len(modules),'declarations':sum(len(v) for v in names.values()),'duplicate_names':len(dups),'max_names_per_batch':100,'batches':batches,'candidates':dict(dups)}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
(a.staging/'plan.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
print('modules',len(modules),'declarations',manifest['declarations'],'duplicates',len(dups),'batches',len(batches))
