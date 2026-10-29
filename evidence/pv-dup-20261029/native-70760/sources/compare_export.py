"""Exact string comparisons over raw elaborated Expr representations, not digest equality."""
from pathlib import Path
import json,zlib,hashlib,collections,time
B=Path(__file__).resolve().parent
coll=json.load(open(B/'collisions.json'));wanted={x['name']:set(x['modules']) for x in coll}
# Within a split object the last available part is authoritative for a declaration.
# Exporter order is public, server, private; our run has at most one record per provider
# in the current non-module project objects, but overwrite semantics also handles splits.
providers={};variants={};stats=collections.Counter();start=time.monotonic()
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
for line in (B/'lean-70764/stdout.log').open():
 if not line.startswith('{'):continue
 x=json.loads(line);n=x['name'];m=x['module'];assert m in wanted[n]
 sig=json.dumps([x['type'],x['value'],x['level_params']],separators=(',',':'),ensure_ascii=False)
 vs=variants.setdefault(n,[]);index=None
 for i,v in enumerate(vs):
  # Decompression and full byte/string equality establish identity; SHA alone is not used.
  if zlib.decompress(v['raw']).decode()==sig:index=i;break
 if index is None:
  index=len(vs);vs.append({'raw':zlib.compress(sig.encode(),1),'type_sha256':sha(x['type']),'value_sha256':sha(json.dumps(x['value'],ensure_ascii=False,separators=(',',':'))),'levels':x['level_params']})
 providers.setdefault(n,{})[m]=index
 stats['export_rows']+=1
result=[];diffs=[];pair_counts=collections.Counter()
for c in coll:
 n=c['name'];p=providers[n];assert set(p)==wanted[n],(n,'missing provider',wanted[n]-set(p))
 groups=[];vs=variants[n]
 for i,v in enumerate(vs):
  mods=sorted(m for m,j in p.items() if i==j)
  if mods:groups.append({'variant_index':i,'modules':mods,**{k:x for k,x in v.items() if k!='raw'}})
 parsed=[json.loads(zlib.decompress(v['raw'])) for v in vs]
 comparisons=[]
 for i in range(len(groups)):
  for j in range(i+1,len(groups)):
   # Compare representatives directly again; no hash-collision assumption.
   a=json.loads(zlib.decompress(vs[groups[i]['variant_index']]['raw']));b=json.loads(zlib.decompress(vs[groups[j]['variant_index']]['raw']))
   comparisons.append({'left_group':i,'right_group':j,'type_equal':a[0]==b[0],'value_equal':a[1]==b[1],'level_params_equal':a[2]==b[2]})
 entry={'name':n,'provider_modules':sorted(p),'identical_type_and_value':len(groups)==1,'groups':groups,'between_groups':comparisons,'within_group':'all elaborated type/value strings and level parameters compared exactly equal'}
 result.append(entry)
 if len(groups)>1:
  diffs.append(entry)
  # Raw expressions for divergent representatives, sufficient to review each disagreement.
  with (B/'divergent-expressions.jsonl').open('a') as f:
   f.write(json.dumps({'name':n,'groups':[{'modules':g['modules'],'type':parsed[g['variant_index']][0],'value':parsed[g['variant_index']][1],'level_params':parsed[g['variant_index']][2]} for i,g in enumerate(groups)]},ensure_ascii=False,separators=(',',':'))+'\n')
 for a in p:
  for b in p:
   if a>=b:continue
   va=parsed[p[a]];vb=parsed[p[b]]
   pair_counts['all_pairs']+=1
   pair_counts['identical_pairs' if va==vb else 'nonidentical_pairs']+=1
   if va[0]!=vb[0]:pair_counts['type_different_pairs']+=1
   if va[1]!=vb[1]:pair_counts['value_different_pairs']+=1
(B/'CENSUS.json').write_text(json.dumps(result,indent=2)+'\n')
(B/'nonidentical.json').write_text(json.dumps(diffs,indent=2)+'\n')
summary={'collision_names':len(result),'identical_names':len(result)-len(diffs),'nonidentical_names':len(diffs),'nonidentical_name_list':[x['name'] for x in diffs],**pair_counts,**stats,'wall_seconds':time.monotonic()-start,'method':'exact canonical constructor DAGs including binder names and metadata; compare bytes directly, then hash for receipt'}
(B/'comparison-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
