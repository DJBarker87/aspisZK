from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;by={}
for p in sorted(E.glob('NHU_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:by[r['module']]=r
mods=[];roots=[];module_rows=[]
for p in sorted(E.glob('NHU_*.lean')):
 if p.stem=='NHU_COMBINED_IMPORT' or not re.search(r'^theorem ',p.read_text(),re.M):continue
 r=by[p.stem];sha=hashlib.sha256(p.read_bytes()).hexdigest();assert r['source_hashes']['NHU_generated/'+p.name]==sha,p
 mods.append(p.stem);module_rows.append(dict(module=p.stem,attempt=r['attempt'],sha256=sha))
 for line in r['print_axioms']:
  m=re.match("'([^']+)'",line)
  if m and m[1] not in roots:roots.append(m[1])
(E/'NHU_MODULES.json').write_text(json.dumps(module_rows,indent=1)+'\n')
a=json.loads((E/'NHU_AUDIT_ROOTS.json').read_text());assert len(a['groups'])==1
old=set(a['groups'][0]);new=[r for r in roots if r not in old];a['groups'] += [new[i:i+12] for i in range(0,len(new),12)]
(E/'NHU_AUDIT_ROOTS.json').write_text(json.dumps(a,indent=1)+'\n')
combined=E/'NHU_COMBINED_IMPORT.lean';body=combined.read_text();prints='\n'.join(l for l in body.splitlines() if l.startswith('#print'))
imports=list(dict.fromkeys(['NGK_COMBINED_IMPORT','NHG_COMBINED_IMPORT','NHN_COMBINED_IMPORT',*mods]))
combined.write_text('\n'.join('import '+m for m in imports)+'\n'+prints+'\n')
rows={r['module']:r for r in map(json.loads,(E/'NHU_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for name in [*mods,'NHU_COMBINED_IMPORT']:
 src=(E/(name+'.lean')).read_text();rows[name]=dict(module=name,imports=['Init',*re.findall(r'^import ([\w.]+)',src,re.M)])
(E/'NHU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[k])+'\n' for k in sorted(rows)))
print(json.dumps(dict(modules=len(mods),new_roots=len(new),batches=len(a['groups'])-1)))
