from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent;R=E.parents[1];p=json.loads((E/'RPz3_source-plan.json').read_text());out={}
for m in p['unresolved']:
 x=p['modules'][m]
 if not x['candidates']:continue
 rows=[]
 for f in x['candidates']:
  s=(R/f).read_text();rows.append({'path':f,'sha256':hashlib.sha256(s.encode()).hexdigest(),'imports':re.findall(r'^import (.+)$',s,re.M),'lines':len(s.splitlines()),'source_directory':'/sources/' in f,'raw_generated':'/extraction/' in f or '/generated/' in f})
 out[m]=rows
(E/'RPz3_source-ambiguities.json').write_text(json.dumps(out,indent=2)+'\n')
for m,rows in out.items():
 print(m)
 for r in rows:print(' ',r['sha256'][:10],r['lines'],'sources' if r['source_directory'] else 'other',r['path'])
