from pathlib import Path
import json,itertools,collections,hashlib
B=Path(__file__).resolve().parent
rows={}
for line in (B/'lean-70754/stdout.log').open():
 if line.startswith('{'):
  d=json.loads(line);rows[d['module']]=d
roots=['PV_EVH_Deployed','PV_RJ4IDB_CallerLive','NDR_CombinedAudit']
closure=set();todo=roots.copy()
while todo:
 m=todo.pop()
 if m in closure:continue
 assert m in rows,('missing module',m)
 closure.add(m);todo.extend(rows[m]['imports'])
first={};dups={};n=0;extra_first={};extra_dups={}
for m in sorted(closure):
 for key,seen,coll in [('names',first,dups),('extras',extra_first,extra_dups)]:
  for name in set(rows[m][key]):
   if key=='names':n+=1
   if name in seen:coll.setdefault(name,[seen[name]]).append(m)
   else:seen[name]=m
out=[];pairs=[]
for name,mods in sorted(dups.items()):
 out.append({'name':name,'modules':mods})
 for a,b in itertools.combinations(mods,2):pairs.append('\t'.join([name,a,rows[a]['path'],b,rows[b]['path']]))
(B/'collisions.json').write_text(json.dumps(out,indent=2)+'\n')
(B/'pairs.tsv').write_text('\n'.join(pairs)+'\n' if pairs else '')
(B/'codegen-name-collisions.json').write_text(json.dumps(extra_dups,indent=2)+'\n')
(B/'closure.json').write_text(json.dumps({'roots':roots,'modules':[{'module':m,'path':rows[m]['path'],'imports':sorted(set(rows[m]['imports'])),'declared_constant_count':len(set(rows[m]['names'])),'extra_codegen_count':len(set(rows[m]['extras']))} for m in sorted(closure)]},indent=2)+'\n')
pairgroups=collections.Counter(tuple(x['modules']) for x in out)
summary={'objects_scanned':len(rows),'closure_modules':len(closure),'unreachable_scanned':sorted(set(rows)-closure),'declaration_occurrences':n,'unique_names':len(first),'duplicate_names':len(dups),'comparison_pairs':len(pairs),'codegen_extra_duplicate_names':len(extra_dups),'module_groups':[{'modules':list(k),'names':v} for k,v in pairgroups.items()]}
(B/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
